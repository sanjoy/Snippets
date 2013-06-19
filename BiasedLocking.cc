#include <pthread.h>
#include <unistd.h>

#include <cassert>
#include <cstdlib>

#include <atomic>
#include <mutex>
#include <thread>

#include "nanotimer.hpp"

using namespace std;
using namespace utils;

const bool kCheckThoroughly = false;

static void ArbitraryDelay() {
  if (kCheckThoroughly) usleep(rand() % 3);
}

#define CompareAndSwapBool(ptr, oldval, newval)         \
  __sync_bool_compare_and_swap(ptr, oldval, newval)

#define UNLIKELY(condition) __builtin_expect(condition, 0)
#define LIKELY(condition)   __builtin_expect(condition, 1)
#define MemoryBarrier __sync_synchronize
#define SequentiallyConsistentLoad(ptr) __atomic_load_n(ptr, __ATOMIC_SEQ_CST)
#define SequentiallyConsistentStore(ptr, value)         \
  __atomic_store_n(ptr, value, __ATOMIC_SEQ_CST)
#define AcquireLoad(ptr) __atomic_load_n(ptr, __ATOMIC_ACQUIRE)
#define ReleaseStore(ptr, value) __atomic_store_n(ptr, value, __ATOMIC_RELEASE)

const long kBackoffUsecsInitialDelay = 5;
const long kBackoffUsecsDelayLimit = 1024 * 8;

#define SPIN_WITH_EXPONENTIAL_BACKOFF(condition) do {                   \
    useconds_t backoff = kBackoffUsecsInitialDelay;                     \
    while (condition) {                                                 \
      usleep(backoff);                                                  \
      if (backoff < (kBackoffUsecsDelayLimit / 2)) backoff *= 2;        \
    }                                                                   \
  } while(false)

class BiasedLock {
 public:
  BiasedLock() :
      state_(kStateUnbiased), revoke_requested_(false) { }

  void lock() {
    useconds_t failed_revoking_delay = kBackoffUsecsInitialDelay;

 retry:
    switch (AcquireLoad(&state_)) {
      case kStateUnbiased:
        if (!CompareAndSwapBool(&state_, kStateUnbiased,
                                kStateBiasedAndLocked)) {
          goto retry;
        }

        biasing_thread_id_ = this_thread::get_id();
        break;

      case kStateBiasedAndLocked:
        assert(biasing_thread_id_ != this_thread::get_id() &&
               "this lock is non-recurrent");
        SPIN_WITH_EXPONENTIAL_BACKOFF(
            AcquireLoad(&state_) == kStateBiasedAndLocked);
        goto retry;

      case kStateBiasedAndUnlocked:
        if (biasing_thread_id_ == this_thread::get_id()) {
          ReleaseStore(&state_, kStateBiasedAndLocked);
          if (UNLIKELY(SequentiallyConsistentLoad(&revoke_requested_))) {
            ReleaseStore(&state_, kStateDefault);
            goto retry;
          }
        } else {
          SequentiallyConsistentStore(&revoke_requested_, true);
          bool result =
              CompareAndSwapBool(&state_, kStateBiasedAndUnlocked,
                                 kStateDefault);
          if (UNLIKELY(!result)) {
            usleep(failed_revoking_delay);
            if (failed_revoking_delay < (kBackoffUsecsDelayLimit / 2)) {
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
    switch (AcquireLoad(&state_)) {
      case kStateBiasedAndLocked:
        ReleaseStore(&state_, kStateBiasedAndUnlocked);
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
  enum {
    kStateUnbiased,
    kStateBiasedAndLocked,
    kStateBiasedAndUnlocked,
    kStateDefault
  };

  mutex base_lock_;
  thread::id biasing_thread_id_;

  volatile unsigned state_;
  volatile bool revoke_requested_;
};

template<typename LockTy>
static void test_thread_body(LockTy *the_lock, volatile bool *shared_flag,
                             const int iterations_count,
                             const int ms_wait_time) {
  for (int i = 0; i < iterations_count; i++) {
    if (ms_wait_time != 0) usleep(1000 * ms_wait_time);

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

template<typename LockTy>
static void simple_bench(string kind, int iterations_count,
                         int second_thread_wait_time_ms) {
  NanoTimer timer(kind);
  volatile bool shared_flag = false;
  LockTy the_lock;

  thread fast_thread(test_thread_body<LockTy>, &the_lock, &shared_flag,
                     iterations_count, 0);
  thread slow_thread_a(test_thread_body<LockTy>, &the_lock, &shared_flag, 1,
                       second_thread_wait_time_ms);
  thread slow_thread_b(test_thread_body<LockTy>, &the_lock, &shared_flag, 1,
                       second_thread_wait_time_ms);

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
    simple_bench<mutex>("simple_bench; pthread_lock", kIterationCount,
                        14);
    simple_bench<BiasedLock>("simple_bench; biased_lock", kIterationCount,
                             14);
    /// The following should call abort(), if kCheckThoroughly is true
    // simple_bench<NoLock>("simple_bench; no_lock", kIterationCount);
  }
}
