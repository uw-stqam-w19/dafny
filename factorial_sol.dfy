function fact (n :int) : int
  requires n > 0;
{
  if (n == 1) then 1 else n * fact (n-1)
}

method factorial_simple (n: int) returns (v:int)
  requires n > 0;
  ensures v == fact(n);
{
  v := 1;
  if (n == 1) { return v; }
  
  var i := 2;
  while (i <= n)
    invariant i <= n+1;
    invariant v == fact(i-1);
  {
    v := i * v;
    i := i + 1;
  }
  return v;
}

method factorial_turing (n: int) returns (v: int)
  requires n > 0;
  ensures v == fact(n);
{
  var r := 1;
  var u := 1;

  while (true)
    decreases n - r;
    invariant u == fact(r);
    invariant r <= n;
  {
    v := u;
    if (r - n >= 0)
    { assert (r == n); return v; }
    var s := 1;
    while (true)
      decreases r + 1 - s
      invariant s <= r < n
      invariant u == s*fact(r)
    {
      u := u + v;
      s := s + 1;
      if ((s - (r + 1)) >= 0)
      {
        assert (s == r+1);
        break;
      }
    }
    r := r + 1;
  }
}

