#define N 10
chan c = [1] of {pid, int};

active [2] proctype P() {
    int n;
    do
        ::eval(_pid);
        ::c?n; c!(n+1)%N; 1-_pid, (n+1)%N;      
        ::timeout -> assert(false)
    od
}

init {
    c!0
}