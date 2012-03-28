#include <iostream>
#include <utility>
#include <vector>

template<class T>
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

template<class A, class B, class C>
struct Func2 {
  typedef C functionType(A, B);
};

template<class T, class N>
struct List {
  T data;
  List<T, P(N)> next;

  template<class A>
  A foldl(typename Func2<A, T, A>::functionType f, A a) {
    return next.foldl(f, f(a, data));
  }
};

template<class T>
struct List<T, Z> {
  template<class A>
  A foldl(typename Func2<A, T, A>::functionType f, A a) {
    return a;
  }
};

template<class T, class N>
List<T, S<N> > push(List<T, N> prev, T &data) {
  List<T, S<N> > newHead;
  newHead.next = prev;
  return newHead;
};

template<class T, class N>
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

template<class T>
struct Sorter<T, S<Z> > {
  static void sort(List<T, S<Z> > &list) { };
};

template<class N>
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

template<class T>
std::vector<T> accumulate(std::vector<T> in, T t) {
  in.push_back(t);
  return in;
}

template<class T, class Out>
void printVector(std::vector<T> v, Out &out) {
  for (typename std::vector<T>::const_iterator i = v.begin(), e = v.end();
       i != e; ++i)
    out << *i << " ";
}

void SortTest() {
  typedef ToType<100>::TypeValue hundred;
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
