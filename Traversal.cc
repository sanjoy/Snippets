#include <cassert>
#include <cstring>
#include <iostream>
#include <stdint.h>
#include <vector>

/* A variation on Thorelli's algorithm.  This (MyTraverse) currently
 * only works on trees, but can probably be made on arbitrary DAGs
 * too.  That's for another afternoon. :)

 * Note that this is not a _pure_ graph theoretic algorithm -- I don't
 * even think it is possible to implement something like this in
 * Python or Java.  One very crucial requirement I have here is the
 * alignment of data structures being >= 2 bytes.
 */

using namespace std;

struct Node {
  /* Used only by BFS. */
  bool Marked;
  int Value;
  vector<Node *>Children;
};

/* <Utilities> */

#ifndef NDEBUG
#define DEBUG_NODE(string, node) do {                           \
    if (node)                                                   \
      cerr << string << " : Node = " << (node)->Value << "  "   \
           << (void *) node << endl;                            \
    else                                                        \
      cerr << string << " : Node = (nil)" << endl;              \
  } while(0)
#else
#define DEBUG_NODE(x, y) do { } while (0)
#endif

template<class T>
void MarkPtr(T *&Ptr) {
  uintptr_t Address = reinterpret_cast<uintptr_t>(Ptr);
  Address |= (uintptr_t) 1;
  Ptr = reinterpret_cast<T *>(Address);
}

template<class T>
void UnmarkPtr(T *&Ptr) {
  uintptr_t Address = reinterpret_cast<uintptr_t>(Ptr);
  Address &= (~(uintptr_t) 1);
  Ptr = reinterpret_cast<T *>(Address);
}

template<class T>
bool IsMarkedPtr(T *Ptr) {
  uintptr_t Address = reinterpret_cast<uintptr_t>(Ptr);
  return (Address & (uintptr_t) 1) != 0;
}

vector<Node *>::iterator FindFirstNonMarked(Node *Root) {
  for (vector<Node *>::iterator i = Root->Children.begin();
       i != Root->Children.end();
       ++i) {
    if (!IsMarkedPtr(*i))
      return i;
  }
  return Root->Children.end();
}

/* </Utilities> */

/* This is called on each node. */
void Do(Node *Value) {
  cout << Value->Value << " ";
}

/* The main traverse function.  Traverses the tree in depth first
 * order, invoking `Do' on each node.
 *
 * Note that this leaves the tree in a mutated, unusable state.  This
 * is easily fixed, though -- we need a "sanitize" function which
 * traverses the tree in exactly the same way as MyTraverse, except
 * that it
 *
 * a. Does not call "Do".
 * b. Uses MarkPtr, UnmarkPtr and IsMarkedPtr in exactly the opposite
 * way as MyTraverse.
 *
 * It could even be possible to templatize (or otherwise parameterize)
 * this function itself to do both.
 */
void MyTraverse(Node *Root) {
  Node *Parent = 0, *Current = Root, *LastChild = 0;
  Do(Root);

  while (Current != 0) {
    assert(!IsMarkedPtr(Current));
    assert(!IsMarkedPtr(Parent));

    DEBUG_NODE("Current", Current);

    vector<Node *>::iterator i = FindFirstNonMarked(Current);

    if (i != Current->Children.end()) {
      DEBUG_NODE("Chosen child ", *i);
      Do(*i);

      if (i != Current->Children.begin()) {
        Parent = *(i - 1);
        MarkPtr(LastChild);
        *(i - 1) = LastChild;
      } /* Else Parent already stores the correct parent.  It is the
         * responsibility of the parent to set the Parent variable
         * before changing Current. */

      Node *Child = *i;
      *i = Parent;
      MarkPtr(*i);
      Parent = Current;
      Current = Child;
    } else {
      if (Current->Children.size() != 0) {
        Parent = *(i - 1);
        UnmarkPtr(Parent);
        assert(!IsMarkedPtr(LastChild));
        MarkPtr(LastChild);
        Current->Children[Current->Children.size() - 1] = LastChild;
      }
      LastChild = Current;
      Current = Parent;
    }
  }
}

/* Just for checking. */
void DfsTraverse(Node *Root) {
  if (Root->Marked)
    return;

  Do(Root);
  Root->Marked = true;
  for (vector<Node *>::iterator i = Root->Children.begin();
       i != Root->Children.end();
       i++) {
    DfsTraverse(*i);
  }
}

/* Read a graph from a textual representation. */
Node *ReadGraph(istream &in) {
  /* Format is  ({ ... } are "comments")

     [Number of Nodes]

     { Node 0 } [Number of children of Node 0] [Child 0] [Child 1] ...
     { Node 1 } ...
           ....
     { Node N }
   */
  size_t NumNodes;
  in >> NumNodes;

  Node *Nodes = new Node[NumNodes];

  for (size_t i = 0; i < NumNodes; i++) {
    int NumChildren;
    in >> NumChildren;
    Nodes[i].Value = i;
    Nodes[i].Marked = false;

    for (int j = 0; j < NumChildren; j++) {
      int Child;
      in >> Child;

      Nodes[i].Children.push_back(&Nodes[Child]);
    }
  }

  return &Nodes[0];
}

int main(int argc, char **argv) {
  bool Regular = (argc > 1 && strcmp(argv[1], "--regular"));

  Node *Graph = ReadGraph(cin);

  cout << "DFS using " << (Regular ?"vanilla algorithm":"Thorelli variant")
       << endl;

  if (Regular)
    DfsTraverse(Graph);
  else
    MyTraverse(Graph);

  cout << endl;
  return 0;
}
