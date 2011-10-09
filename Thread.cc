#include <cassert>
#include <iostream>
#include <stdint.h>
#include <vector>

using namespace std;

#define NUM_WORDS 4

bool IsPointer(uintptr_t Value) {
  return (Value & ((uintptr_t) 1)) == 0;
}

struct Node {
  uintptr_t Content[NUM_WORDS];

  void setHeader(int value) {
    Content[0] = static_cast<uintptr_t>(value);
    Content[0] <<= 2;
    Content[0] |= 1;
  }

  int getHeader() {
    uintptr_t Tmp = Content[0] >> 2;
    return static_cast<int>(Tmp);
  }

  bool isHeaderPointer() {
    return IsPointer(Content[0]);
  }

  Node *headerAsPointer() {
    return reinterpret_cast<Node *>(Content[0]);
  }
};

void Thread(vector<Node *>& Heap) {
  for (vector<Node *>::iterator i = Heap.begin();
       i != Heap.end();
       ++i) {
    for (size_t word = 1; word < NUM_WORDS; word++) {
      if ((*i)->Content[word] != 0) {
        Node *Pointee = reinterpret_cast<Node *>((*i)->Content[word]);
        (*i)->Content[word] = Pointee->Content[0];
        Pointee->Content[0] = reinterpret_cast<uintptr_t>(*i) +
                              word * sizeof(uintptr_t);
      }
    }
  }
}

void ShowLinkage(vector<Node *>& Heap) {
  for (vector<Node *>::iterator i = Heap.begin();
       i != Heap.end();
       ++i) {
    uintptr_t Tmp = (*i)->Content[0];

    cout << "[ ";
    while (Tmp && IsPointer(Tmp)) {
      cout << reinterpret_cast<void *>(Tmp) << " ";
      Tmp = *reinterpret_cast<uintptr_t *>(Tmp);
    }

    cout << "] -> " << (Tmp >> 2) << endl;
  }
}

vector<Node *> ReadGraph(istream &in) {
  /* Format is  ({ ... } are "comments")

     [Number of Nodes]

     { Node 0 } [Number of children of Node 0] [Child 0] [Child 1] ...
     { Node 1 } ...
           ....
     { Node N }
   */
  size_t NumNodes;
  in >> NumNodes;

  vector<Node *> Nodes(NumNodes);
  for (vector<Node *>::iterator i = Nodes.begin(); i != Nodes.end(); ++i)
    *i = new Node;

  for (size_t i = 0; i < NumNodes; i++) {
    int NumChildren;
    in >> NumChildren;
    Nodes[i]->setHeader(i);

    assert(NumChildren < (NUM_WORDS - 1) &&
           "Only NUM_WORDS - 1 children allowed.");

    for (int j = 0; j < NumChildren; j++) {
      int Child;
      in >> Child;

      Nodes[i]->Content[j + 1] = reinterpret_cast<uintptr_t>(Nodes[Child]);
    }
  }

  return Nodes;
}

int main() {
  vector<Node *>Graph = ReadGraph(cin);
  Thread(Graph);
  ShowLinkage(Graph);
  return 0;
}
