#include <cassert>
#include <cstdlib>

#include <atomic>
#include <chrono>
#include <functional>
#include <mutex>
#include <thread>

#include "nanotimer.hpp"

#define UNLIKELY(condition) __builtin_expect(condition, 0)
#define LIKELY(condition)   __builtin_expect(condition, 1)

using namespace std;
using namespace utils;

const bool kCheckThoroughly = false;

static void ArbitraryDelay() {
  if (kCheckThoroughly) {
    this_thread::sleep_for(chrono::microseconds(rand() % 3));
  }
}

const std::chrono::microseconds kBackoffInitialDelay(5);
const std::chrono::microseconds kBackoffDelayLimit(1000 * 8);

#define SPIN_WITH_EXPONENTIAL_BACKOFF(condition) do {                   \
    auto backoff = kBackoffInitialDelay;                                \
    while (condition) {                                                 \
      std::this_thread::sleep_for(backoff);                             \
      if (backoff < (kBackoffDelayLimit / 2)) backoff *= 2;             \
    }                                                                   \
  } while(false)

class BiasedLock {
 public:
  BiasedLock() : state_(kStateUnbiased), revoke_requested_(false) { }

  void lock() {
    auto failed_revoking_delay = kBackoffInitialDelay;

 retry:
    switch (state_.load(memory_order_acquire)) {
      case kStateUnbiased: {
        unsigned expected = kStateUnbiased;
        if (!state_.compare_exchange_weak(expected, kStateBiasedAndLocked)) {
          goto retry;
        }

        biasing_thread_id_.store(this_thread::get_id(), memory_order_release);
        break;
      }

      case kStateBiasedAndLocked:
        assert(biasing_thread_id_.load() != this_thread::get_id() &&
               "this lock is non-recurrent");
        SPIN_WITH_EXPONENTIAL_BACKOFF(
            state_.load(memory_order_acquire) == kStateBiasedAndLocked);
        goto retry;

      case kStateBiasedAndUnlocked:
        if (biasing_thread_id_.load(memory_order_acquire) ==
            this_thread::get_id()) {
          state_.store(kStateBiasedAndLocked, memory_order_release);
          if (UNLIKELY(revoke_requested_.load())) {
            state_.store(kStateDefault, memory_order_release);
            goto retry;
          }
        } else {
          revoke_requested_.store(true);
          unsigned expected = kStateBiasedAndUnlocked;
          bool result = state_.compare_exchange_strong(expected, kStateDefault);
          if (UNLIKELY(!result)) {
            this_thread::sleep_for(failed_revoking_delay);
            if (failed_revoking_delay < (kBackoffDelayLimit / 2)) {
              failed_revoking_delay *= 2;
            }
          }
          goto retry;
        }
        break;

      case kStateDefault:
        base_lock_.lock();
        break;
    }
  }

  void unlock() {
    switch (state_.load(memory_order_acquire)) {
      case kStateBiasedAndLocked:
        state_.store(kStateBiasedAndUnlocked, memory_order_release);
        break;

      case kStateDefault:
        base_lock_.unlock();
        break;

      default:
        assert(0 && "not reached!");
        break;
    }
  }

 private:
  mutex base_lock_;

  enum {
    kStateUnbiased,
    kStateBiasedAndLocked,
    kStateBiasedAndUnlocked,
    kStateDefault
  };

  atomic<thread::id> biasing_thread_id_;
  atomic<unsigned> state_;
  atomic_bool revoke_requested_;
};

template<typename LockTy, typename DurationTy>
static void test_thread_body(LockTy *the_lock, volatile bool *shared_flag,
                             const int iterations_count,
                             const DurationTy wait_time) {
  for (int i = 0; i < iterations_count; i++) {
    if (wait_time != DurationTy::zero()) {
      this_thread::sleep_for(wait_time);
    }

    the_lock->lock();

    ArbitraryDelay();
    if (UNLIKELY(*shared_flag)) goto no_mutex;

    *shared_flag = true;
    ArbitraryDelay();
    if (UNLIKELY(!*shared_flag)) goto no_mutex;

    *shared_flag = false;
    ArbitraryDelay();
    if (UNLIKELY(*shared_flag)) goto no_mutex;

    the_lock->unlock();
  }
  return;

no_mutex:
  printf("error: no mutual exclusion!");
  abort();
}

template<typename LockTy, typename DurationTy>
static void simple_bench(const string kind, const int iterations_count,
                         const DurationTy second_thread_wait_time) {
  NanoTimer timer(kind);
  volatile bool shared_flag = false;
  LockTy the_lock;

  thread fast_thread(test_thread_body<LockTy, DurationTy>, &the_lock,
                     &shared_flag, iterations_count, DurationTy::zero());
  thread slow_thread_a(test_thread_body<LockTy, DurationTy>, &the_lock,
                       &shared_flag, 1, second_thread_wait_time);
  thread slow_thread_b(test_thread_body<LockTy, DurationTy>, &the_lock,
                       &shared_flag, 1, second_thread_wait_time);

  fast_thread.join();
  slow_thread_a.join();
  slow_thread_b.join();
}

class NoLock {
 public:
  void lock() {}
  void unlock() {}
};

int main() {
  const int kIterationCount = kCheckThoroughly ? 1024 : (1024 * 1024);
  while (true) {
    simple_bench<mutex, chrono::milliseconds>("simple_bench; standard_lock",
                                              kIterationCount,
                                              chrono::milliseconds(14));
    simple_bench<BiasedLock, chrono::milliseconds>("simple_bench; biased_lock",
                                                   kIterationCount,
                                                   chrono::milliseconds(14));
    /// The following should call abort(), if kCheckThoroughly is true
    // simple_bench<NoLock>("simple_bench; no_lock", kIterationCount);
  }
}
