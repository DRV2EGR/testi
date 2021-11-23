#include <stdio.h>
#include <stdbool.h>
 
 /*@
  requires \valid(limit);

  requires limit > 2 ==> printf("2 ")
  requires limit > 3 ==> printf("3 ")

  assigns  a[0..n-1];

  \forall integer i;
    0 <= i < limit ==> sieve[i] == 0;
*/
int solve_task(int limit)
{
    // 2 and 3 are known to be prime
    if (limit > 2) {
        printf("2 ");
    }
    if (limit > 3) {
        printf("3 ");
    }
 
    bool sieve[limit];

    /*@
        loop invariant 0 <= i <= limit;
        loop invariant \forall size_t j; 0 <= j < i ==> sieve[j] = true;
        loop assigns i;
        loop variant limit-1;
    */
    for (int i = 0; i < limit; i++)
        sieve[i] = false;
 
    for (int x = 1; x * x < limit; x++) {
        for (int y = 1; y * y < limit; y++) {
             
            // Main part of Sieve of Atkin
            int n = (4 * x * x) + (y * y);
            if (n <= limit && (n % 12 == 1 || n % 12 == 5))
                sieve[n] ^= true;
 
            n = (3 * x * x) + (y * y);
            if (n <= limit && n % 12 == 7)
                sieve[n] ^= true;
 
            n = (3 * x * x) - (y * y);
            if (x > y && n <= limit && n % 12 == 11)
                sieve[n] ^= true;
        }
    }
 
    for (int r = 5; r * r < limit; r++) {
        if (sieve[r]) {
            for (int i = r * r; i < limit; i += r * r)
                sieve[i] = false;
        }
    }
 
    /*@
        loop invariant 0 <= a <= limit;
        loop invariant \forall size_t j; 0 <= j < a ==> sieve[j] != true;
        loop assigns a;
        loop variant limit-1;
    */
    for (int a = 5; a < limit; a++)
        if (sieve[a]) {
            printf("%d ", a);
        }
}
 
int main(void)
{
    int limit = 20;
    /*@ assert \ valid(limit); */
    solve_task(limit);
    return 0;
}