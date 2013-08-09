#ifndef __NANOTIMER__HPP
#define __NANOTIMER__HPP

#include <sys/time.h>
#include <unistd.h>

#include <cstdio>
#include <string>

namespace utils {

class NanoTimer {
 public:
  NanoTimer(const std::string &prefix) : prefix_(prefix) {
    gettimeofday(&start_, NULL);
  }

  ~NanoTimer() {
    gettimeofday(&end_, NULL);
    long seconds = end_.tv_sec  - start_.tv_sec;
    long useconds = end_.tv_usec - start_.tv_usec;
    double mtime = ((seconds) * 1000 + useconds/1000.0) + 0.5;
    std::printf("%s: %0.3lf milliseconds\n", prefix_.c_str(), mtime);
  }

 private:
  timeval start_, end_;
  std::string prefix_;
};

} // namespace utils

#endif // __NANOTIMER__HPP
