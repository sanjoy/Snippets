#include <pthread.h>
#include <unistd.h>

#include <cassert>
#include <cstdlib>

#include "nanotimer.hpp"

using namespace std;
using namespace utils;

#define CompareAndSwapBool(ptr, oldval, newval)         \
  __sync_bool_compare_and_swap(ptr, oldval, newval)

#define UNLIKELY(condition) __builtin_expect(condition, 0)
#define LIKELY(condition)   __builtin_expect(condition, 1)
#define MemoryBarrier __sync_synchronize
#define SequentiallyConsistentLoad(ptr) __atomic_load_n(ptr, __ATOMIC_SEQ_CST)

const long kBackoffUsecsInitialDelay = 5;
const long kBackoffUsecsDelayLimit = 1024 * 8;

#define SPIN_WITH_EXPONENTIAL_BACKOFF(condition) do {           \
    useconds_t backoff = kBackoffUsecsInitialDelay;             \
    while (condition) {                                         \
      usleep(backoff);                                          \
      if (backoff < kBackoffUsecsDelayLimit) backoff *= 2;      \
    }                                                           \
  } while(false)

class PthreadLock {
 public:
  PthreadLock() {
    pthread_mutex_init(&mutex_, NULL);
  }

  void lock() {
    pthread_mutex_lock(&mutex_);
  }

  void unlock() {
    pthread_mutex_unlock(&mutex_);
  }

  ~PthreadLock() {
    pthread_mutex_destroy(&mutex_);
  }

 private:
  pthread_mutex_t mutex_;
};

class BiasedLock {
 public:
  BiasedLock() : state_(kStateUnbiased),
                 revoke_requested_(false) { }

  void lock() {
    useconds_t failed_revoking_delay = kBackoffUsecsInitialDelay;

 retry:
    switch (state_) {
      case kStateUnbiased:
        if (!CompareAndSwapBool(&state_, kStateUnbiased,
                                kStateBiasedAndLocked)) {
          goto retry;
        }

        thread_id_ = pthread_self();
        break;

      case kStateBiasedAndLocked:
        assert(thread_id_ != pthread_self() && "this lock is non-recurrent");
        SPIN_WITH_EXPONENTIAL_BACKOFF(state_ == kStateBiasedAndLocked);
        goto retry;

      case kStateBiasedAndUnlocked:
        if (thread_id_ == pthread_self()) {
          state_ = kStateBiasedAndLocked;
          if (UNLIKELY(SequentiallyConsistentLoad(&revoke_requested_))) {
            state_ = kStateDefault;
            goto retry;
          }
        } else {
          revoke_requested_ = true;
          MemoryBarrier();
          bool result = CompareAndSwapBool(&state_, kStateBiasedAndUnlocked,
                                           kStateDefault);
          if (UNLIKELY(!result)) {
            usleep(failed_revoking_delay);
            if (failed_revoking_delay < kBackoffUsecsDelayLimit) {
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
    switch (state_) {
      case kStateBiasedAndLocked:
        state_ = kStateBiasedAndUnlocked;
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

  PthreadLock base_lock_;
  pthread_t thread_id_;

  volatile unsigned state_;
  volatile bool revoke_requested_;
};

class Thread {
 public:
  void start() {
    pthread_create(&thread_, NULL, launch_thread, this);
  }

  void* join() {
    void *return_value;
    pthread_join(thread_, &return_value);
    return return_value;
  }

 protected:
  virtual void* run() = 0;

 private:
  pthread_t thread_;

  static void* launch_thread(void *thread_obj) {
    return reinterpret_cast<Thread *>(thread_obj)->run();
  }
};

template<typename LockTy>
class LockingThread : public Thread {
 public:
  LockingThread(LockTy *the_lock, volatile long *shared_location_a,
                volatile long *shared_location_b, const int run_count,
                const int ms_wait_time)
      : the_lock_(the_lock),
        shared_location_a_(shared_location_a),
        shared_location_b_(shared_location_b),
        run_count_(run_count),
        ms_wait_time_(ms_wait_time) { }

 protected:
  virtual void* run() {
    for (int i = 0; i < run_count_; i++) {
      if (ms_wait_time_ != 0) usleep(1000 * ms_wait_time_);

      the_lock_->lock();
      (*shared_location_a_)++;
      (*shared_location_b_)++;
      the_lock_->unlock();
    }
    return NULL;
  }

 private:
  LockTy *the_lock_;
  volatile long *shared_location_a_;
  volatile long *shared_location_b_;
  const int run_count_;
  const int ms_wait_time_;
};

template<typename LockTy>
static void bench_threads(string kind, int iteration_count) {
  NanoTimer timer(kind);
  volatile long shared_location_a = 0, shared_location_b = 0;
  LockTy the_lock;

  LockingThread<LockTy>
      freq_thread(&the_lock, &shared_location_a, &shared_location_b,
                  iteration_count, 0);
  LockingThread<LockTy>
      rare_thread(&the_lock, &shared_location_a, &shared_location_b, 1, 14);

  freq_thread.start();
  rare_thread.start();

  freq_thread.join();
  rare_thread.join();

  if (shared_location_a != (iteration_count + 1) ||
      shared_location_b != (iteration_count + 1)) {
    printf("error: %s failed!\n", kind.c_str());
    abort();
  }
}

int main() {
  const int kIterationCount = 1024 * 1024;
  while (true) {
    bench_threads<PthreadLock>("bench_threads; pthread_lock", kIterationCount);
    bench_threads<BiasedLock>("bench_threads; biased_lock", kIterationCount);
  }
}
