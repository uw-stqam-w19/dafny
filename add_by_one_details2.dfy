function rank(y:int, i:int) : int {
  y - i
}

function inv(i: int, y:int, x:int, r: int) : bool
{
  i <= y &&  r == x + i && rank(y, i) >= 0
}
method add_by_one_2 (x:int, y:int) returns (r:int)
{
  assume(y >= 0);
  var i:int := 0;
  r := x;
  assert(inv(i, y, x, r));

  i, r := *, *;
  assume(inv(i, y, x, r));
  if (i < y)
  {
    ghost var rank0 := rank(y, i);
    r := r + 1;
    i := i + 1;
    ghost var rank1 := rank(y, i);
    assert(inv(i, y, x, r));
    assert (rank1 < rank0);
    assume(false);
  } 
  assert(r == x + y);
  return r;
}



method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{
  var i:int := 0;
  r := x;
  while (i < y)
  decreases y - i;
  invariant i <= y ;
  invariant r == x + i;
  {
    assume(i <= 2);
    r := r + 1;
    i := i + 1;
  }
  return r;
}















































/* function rank(i: int, y:int) : int
{y - i}

function inv(i: int, x:int, y:int, r:int ) : bool
{i <= y && r == x + i && rank(i, y) >= 0}

method add_by_one_detail (x:int, y:int)
  returns (r:int)
{
  // pre-condition
  assume(y >= 0);
  var i := 0;
  r := x;

  // base case for invariant
  assert(inv(i, x, y, r));

  // inductive hypothesis
  r, i := *, *;
  assume(inv(i, x, y, r));

  if (i < y)
  {
    // store rank to check that it is decreasing
    ghost var rank0 := rank(i, y);
    r := r + 1;
    i := i + 1;
    // inductive case for invariant
    assert(inv(i, x, y, r));
    // ensure that rank is decreasing
    assert(rank(i, y) < rank0);
    assume(false);
  }

  // at this point:
  //   - the invariant is true
  //   - loop condition is false
  //   - anything not changed by the loop remains as is

  // post-condition
  assert(r == x + y);
  return r;
} */







































