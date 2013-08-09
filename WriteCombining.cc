#include "nanotimer.hpp"

#include <cstdlib>
#include <cstdint>

using namespace std;
using namespace utils;

// http://mechanical-sympathy.blogspot.in/2011/07/write-combining.html
// in C++

namespace {

class Benchmark {
 private:
  static const int kItemCount = 1 << 24;
  static const int kIterations = kItemCount << 4;

  uint8_t *array_a, *array_b, *array_c, *array_d, *array_e, *array_f;

 public:
  Benchmark() {
    array_a = new uint8_t[kItemCount];
    array_b = new uint8_t[kItemCount];
    array_c = new uint8_t[kItemCount];
    array_d = new uint8_t[kItemCount];
    array_e = new uint8_t[kItemCount];
    array_f = new uint8_t[kItemCount];
  }

  void run_single_loop()  __attribute__((noinline)) {
    NanoTimer timer("single_loop");

    for (int i = 0; i < kIterations; i++) {
      int index = i % kItemCount;
      uint8_t value = static_cast<uint8_t>(i);
      array_a[index] = value;
      array_b[index] = value;
      array_c[index] = value;
      array_d[index] = value;
      array_e[index] = value;
      array_f[index] = value;
    }
  }

  void run_split_loop() __attribute__((noinline)) {
    NanoTimer timer("split_loop");

    for (int i = 0; i < kIterations; i++) {
      int index = i % kItemCount;
      uint8_t value = static_cast<uint8_t>(i);
      array_a[index] = value;
      array_b[index] = value;
      array_c[index] = value;
    }

    for (int i = 0; i < kIterations; i++) {
      int index = i % kItemCount;
      uint8_t value = static_cast<uint8_t>(i);
      array_d[index] = value;
      array_e[index] = value;
      array_f[index] = value;
    }
  }

  ~Benchmark() {
    delete []array_a;
    delete []array_b;
    delete []array_c;
    delete []array_d;
    delete []array_e;
    delete []array_f;
  }
};

}

int main() {
  Benchmark b;
  for (int i = 0; i < 3; i++) {
    b.run_single_loop();
    b.run_split_loop();
  }
}
