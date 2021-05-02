#include <cstdlib>
#include <cstdio>

bool malloc_was_called = false;

void* operator new(size_t size) __attribute__((noinline)) {
    malloc_was_called = true;
    return std::malloc(size);
}

bool is_o0() __attribute__((noinline)) {
	malloc_was_called = false;
	delete new int;
	return malloc_was_called;
}

void o2_gvn_gadget(int a, int b) __attribute__((noinline)) {
	static volatile int vol = 0;
	int c = a + 1;
	int d = c;
	if (a == b) {
		vol++;
		d = b + 1;
	}
	static volatile int* escape;
	int* ptr = new int;
	if (c != d) {
		escape = ptr;
	}
	delete ptr;
}

bool is_o2() __attribute__((noinline)) {
	malloc_was_called = false;
	o2_gvn_gadget(10, 20);
	return !malloc_was_called;
}

static void o3_argpromotion_gadget(int& value) __attribute__((noinline)) {
	static volatile int escape;
	escape = value + 10;
}

bool is_o3() __attribute__((noinline)) {
	malloc_was_called = false;
	int* ptr = new int(5);
	o3_argpromotion_gadget(*ptr);
	delete ptr;
	return !malloc_was_called;
}

int main() {
	if (is_o0()) {
		printf("O0\n");
	} else if (is_o3()) {
		printf("O3\n");
	} else if (is_o2()) {
		printf("O2\n");
	} else {
		printf("O1\n");
	}
    return 0;
}