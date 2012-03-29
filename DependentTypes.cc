#include <iostream>
#include <utility>
#include <vector>

template<typename T>
struct S { typedef T Previous;
  enum { ToInt = T::ToInt + 1 };
};

struct Z { enum { ToInt = 0 }; };

template<int N>
struct ToType {
  typedef S<typename ToType<N - 1>::TypeValue > TypeValue;
};

template<>
struct ToType<0> {
  typedef Z TypeValue;
};

#define P(n) typename n::Previous
#define TO_INT(n) n::ToInt
#define TO_TYPE(n) typename ToType<n>::TypeValue

template<typename A, typename B, typename C>
struct Func2 {
  typedef C functionType(A, B);
};

template<typename T, typename N>
struct List {
  T data;
  List<T, P(N)> next;

  template<typename A>
  A foldl(typename Func2<A, T, A>::functionType f, A a) {
    return next.foldl(f, f(a, data));
  }
};

template<typename T>
struct List<T, Z> {
  template<typename A>
  A foldl(typename Func2<A, T, A>::functionType f, A a) {
    return a;
  }
};

template<typename T, typename N>
List<T, S<N> > push(List<T, N> prev, T &data) {
  List<T, S<N> > newHead;
  newHead.next = prev;
  return newHead;
};

template<typename T, typename N>
struct Sorter {
  static void sort(List<T, N> &list) {
    List<T, P(N)> rest = list.next;
    Sorter<T, P(N)>::sort(rest);
    if (list.data > rest.data) {
      std::swap(rest.data, list.data);
      Sorter<T, P(N)>::sort(rest);
    }
    list.next = rest;
  }
};

template<typename T>
struct Sorter<T, S<Z> > {
  static void sort(List<T, S<Z> > &list) { };
};

template<typename N>
struct ListCreator {
  static List<int, N> create() {
    List<int, N> newHead;
    newHead.data = TO_INT(N);
    newHead.next = ListCreator<P(N)>::create();
    return newHead;
  }
};

template<>
struct ListCreator<Z> {
  static List<int, Z> create() { return List<int, Z>();  }
};

template<typename T>
std::vector<T> accumulate(std::vector<T> in, T t) {
  in.push_back(t);
  return in;
}

template<typename T, typename Out>
void printVector(std::vector<T> v, Out &out) {
  for (typename std::vector<T>::const_iterator i = v.begin(), e = v.end();
       i != e; ++i)
    out << *i << " ";
}

void SortTest() {
  typedef TO_TYPE(100) hundred;
  List<int,  hundred> list = ListCreator<hundred>::create();
  std::cout << "Initial list: ";
  {
    printVector(list.foldl(accumulate, std::vector<int>()), std::cout);
  }
  std::cout << std::endl;

  Sorter<int, hundred>::sort(list);
  std::cout << "After sorting: ";
  {
    printVector(list.foldl(accumulate, std::vector<int>()), std::cout);
  }
  std::cout << std::endl;
}

int main() {
  SortTest();
}
