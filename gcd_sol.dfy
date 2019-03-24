/*
   The greatest common divisor (gcd) of two natural numbers m and n is a number k such that
    (a) k divides m; (b) k divides n; and (c) k is the largest number with these properties.

   Define a recursive function that computes a gcd of two numbers using the following properties of gcd.
   (a) gcd(n, n) == n
   (b) gcd(m, n) == gcd(m-n, n) whenever m > n
   (c) gcd(m, n) == gcd(m, n-m) whenever n > m
*/
function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0;
  decreases m + n;
{
  /* your code here */
  if (m == n) then m
  else if (m > n) then gcd(m - n, n)
  else gcd(m, n - m)
}
/**
   Specify and verify a function to compute gcd of m and n
 */
method GcdCalc(m: nat, n: nat) returns (res: nat)
  requires m > 0 && n > 0;
  ensures res == gcd(m, n);
  // your spec here
{
  var n1, m1 := n, m;
  while (n1 != m1)
    decreases m1 + n1;
    invariant m1 > 0 && n1 > 0;
    invariant gcd(m, n) == gcd(m1, n1);
  {
    if (m1 < n1) {
     n1 := n1 - m1;
    } else {
     m1 := m1 - n1;
    }
  }
  assert(m1 == n1);
  return n1;
}






















/* function gcd(m: nat, n: nat): nat
  requires n > 0 && m > 0;
  decreases m + n;
{
  if (n==m) then n
  else if (m>n) then gcd(m-n, n)
  else gcd(m, n-m)
}
*/
















/*
method GcdCal(m: nat, n: nat) returns (res: nat)
  ensures res == gcd(m, n);
{
  var m1: nat, n1: nat := m, n;

  while (m1!=n1)
  {
    if (m1>n1) {
      m1 := m1-n1;
    }
    else {
      n1 := n1-m1;
    }
 }
 return m1;
}
 */









/* gcd lemma: use gcd(m, n) = gcd(n1, m1) */
