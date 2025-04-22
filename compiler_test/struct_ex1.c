#include <stdio.h>

// Define a struct to represent a point in 2D
struct Point {
    int x;
    int y;
};

int main() {
    struct Point p1;       // Declare a variable of type struct Point
    p1.x = 10;             // Assign values to fields
    p1.y = 20;

    printf("Point p1 is at (%d, %d)\n", p1.x, p1.y);
    return 0;
}
