method Max(a: int, b: int) returns (m: int) // wp : a and b are integers
  ensures m == if a > b then a else b // sp : m is the maximum of a and b
{
  if a > b {
    m := a;
  } else {
    m := b;
  }
}

method {:test} TestMax()
{
  var x := Max(2, 3);
  assert x == 3;

  var y := Max(-4, 1);
  assert y == 1;

  var z := Max(0, 0);
  assert z == 0;

}

method Min(a: int, b: int) returns (m: int) // wp : a and b are integers
  ensures m == if a > b then b else a // sp : m is the minimum of a and b
{
  if a > b {
    m := b;
  } else {
    m := a;
  }
}

method {:test} TestMin()
{
  var x := Min(2, 3);
  assert x == 2;

  var y := Min(-4, 1);
  assert y == -4;

  var z := Min(0, 0);
  assert z == 0;
}


method M1(x: int, y: int) returns (r: int)
  // ensures ?
  ensures r == if x == 0 then 0 else r
  decreases x < 0, x
{
  if x == 0 {
    r := 0;
  } else if x < 0 {
    r := M1(-x, y);
    r := -r;
  } else {
    r := M1(x - 1, y);
    r := A1(r, y);
  }
}

method A1(x: int, y: int) returns (r: int)
  // ensures ?
  ensures r == x + y
{
  r := x;
  if y < 0 {
    var n := y;
    while n != 0
      invariant r == x + y - n
      invariant -n >= 0
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while n != 0
      invariant r == x + y - n
      invariant n >= 0
    {
      r := r + 1;
      n := n - 1;
    }
  }
}

method swap(a: array<int>, i: nat, j: nat)
  modifies a

  // requires relationship between i and a.Length
  requires i < a.Length
  // requires relationship between j and a.Length
  requires j < a.Length

  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

method {:main} TestSwap()
{
  var a := new int[] [1, 2, 3, 4];
  assert a[1] == 2 && a[3] == 4;
  swap(a, 1, 3);
  assert a[1] == 4 && a[3] == 2;
  // swap(a, 8, 0); // this should fail as 8 is not less than a.Length
}