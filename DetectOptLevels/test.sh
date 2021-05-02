#!/bin/bash

clang++ --version

echo ""
echo ""

clang++ -w -O0 detect.cc -o detect-o0 && echo "Executing detect-o0" && ./detect-o0
clang++ -w -O1 detect.cc -o detect-o1 && echo "Executing detect-o1" && ./detect-o1
clang++ -w -O2 detect.cc -o detect-o2 && echo "Executing detect-o2" && ./detect-o2
clang++ -w -O3 detect.cc -o detect-o3 && echo "Executing detect-o3" && ./detect-o3