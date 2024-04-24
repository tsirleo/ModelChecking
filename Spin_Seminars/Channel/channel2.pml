  1 #define N 10
  2 
  3 chan c = [1] of {pid, int};
  4 
  5 active [2] proctype P() {
  6     int n;
  7     do
  8         :: c?eval(_pid),n -> c!1 - _pid,(n+1) % N
  9         :: timeout -> assert(false)
 10     od
 11 }
 12 
 13 init {
 14     c!0, 0
 15 }

