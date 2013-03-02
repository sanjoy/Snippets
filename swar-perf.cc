#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <stdint.h>

using namespace std;

static int pop_cnt_swar(uint32_t i) {
  i = i - ((i >> 1) & 0x55555555);
  i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
  return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

static int pop_cnt_builtin(uint32_t i) {
  return __builtin_popcount(i);
}

static void usage(char *name) {
  printf("Usage: %s <count> --swar or --builtin", name);
}

static void run_test(int (*fn) (uint32_t value), int count) {
#define C(x) static_cast<uint32_t>(x)
  static const uint32_t input[] = {
    C(rand()), C(rand()), C(rand()), C(rand()),
    C(rand()), C(rand()), C(rand()), C(rand()),
    C(rand()), C(rand()), C(rand()), C(rand()),
    C(rand()), C(rand()), C(rand()), C(rand())
  };
#undef C

  int input_len = sizeof(input) / sizeof(int);

  for (int i = 0; i < count; i++) {
    fn(input[i % input_len]);
  }
}

int main(int argc, char **argv) {
  if (argc != 3) {
    usage(argv[0]);
    return -1;
  }

  int test_count;
  int result = sscanf(argv[1], "%d", &test_count);
  if (result != 1) {
    usage(argv[0]);
    return -1;
  }

  if (!strcmp(argv[2], "--swar")) {
    run_test(pop_cnt_swar, test_count);
  } else if (!strcmp(argv[2], "--builtin")) {
    run_test(pop_cnt_builtin, test_count);
  } else {
    usage(argv[0]);
    return -1;
  }
}
