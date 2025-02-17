void modify(volatile int *ptr) {
    *ptr = 100;  // Always writes to memory
}

int main() {
    volatile int v = 42;
    modify(&v);   // Pass pointer to volatile
    return 0;
}
