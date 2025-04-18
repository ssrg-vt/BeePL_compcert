 #include <stdio.h>

// Define a struct to represent a point in 2D
struct Point {
    int x;
    int y;
};

int main() {
    struct Point p1;       // Declare a variable of type struct Point
    p1.x = 10;
    return p1.x;
}
