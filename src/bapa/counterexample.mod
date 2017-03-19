/*
   This example shows that we can force 5 variables to be non-zero
   using only 4 equations.  This is not the case for real numbers
   but is the case for integers.  Viktor Kuncak found this example
   in November 2006 by hand, proving first restrictions on
   the form that such examples could take.
*/

/* Using glpsol to find solutions to CBAC constraints */
param m, integer, >= 0, default 5;
/* number of integer variables */

var x{0..m-1}, integer, >= 0;
/* sizes of partitions */

var b{0..m-1}, binary;
/* whether partitions are nonempty */

/*
x1+x2+x3 = 3
x2+x3+x4 = 3
x1+x3+x4+x5=4
x1+x2+x4+x5=4 
*/

s.t. e1: x[0] + x[1] + x[2] = 3;

s.t. e2: x[1] + x[2] + x[3] = 3;

s.t. e3: x[0] + x[2] + x[3] + x[4] = 4;

s.t. e4: x[0] + x[1] + x[3] + x[4] = 4;

s.t. bDef{i in 0..m-1}: x[i] <= 4 * b[i];

minimize obj: sum{i in 0..m-1} b[i];
/* try to get as few non-zero variables as possible */

/* solve the problem */
solve;

/* and print its optimal solution */
display x;
printf "Non-zero solutions:\n";
printf "%d", sum{i in 0..m-1} b[i];
end;
