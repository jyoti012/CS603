//Dafny introductory examples

//Methods:

method Triple(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3*x
{
  var y := x / 2;
  r := 6*y;
  assert r == 3*x; // postcondition is r == 3*x hence it works
}

method Triple0(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3*x
{
  var y;
  assert 6*(x/2)  == 3*x;
  y:= x / 2;
  assert 6*y  == 3*x;
  r := 6*y;
  assert r == 3*x;
}



method Triple1(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3*x
{
  if x == 0 {
    r := 0;
  } else {
    var y := 2*x;
    r := x + y;
  }
  assert r == 3*x;
}


method Triple1_with_asserts(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3*x
{
  assert x % 2 == 0;
  assert x == 0 || x!=0;
  if x == 0 {
    assert x==0;
    assert 0 == 3*x; // weakest precondition if 1st branch body is executed
    r := 0;
    assert r == 3*x;
  } else {
    assert x!=0;
    var y ;
    assert x+(2*x) == 3*x; // weakest precondition if 2nd branch body is executed
    y:= 2*x;
    assert x+y == 3*x;
    r := x + y;
    assert r == 3*x;
  }
  assert r == 3*x;
}



method Triple2(x: int) returns (r: int)
  requires x % 2 == 0
  ensures r == 3*x
{
  if {
    case x < 18 => // guards overlap
      var a, b := 2*x, 4*x; //simultaneous assignment
      r := (a + b) / 2;
    case 0 <= x =>
      var y := 2*x; //scope local to case branch
      r := x + y;
  }
  assert r == 3*x;
}

method Index(n: int) returns (i: int)
  requires 1 <= n
  ensures 0 <= i < n // under specification
{
  i := n / 2;
  //i := 0; // will also work
}



method Main() {
  var t := Triple(18);
  print "The value is ", t, "\n";
  var x := Index(50);
  var y := Index(50);

  //assert x == y;  // error as the assertion cannot be proved, because all we know from the specification of Index is
  //0 <= x < 50 && 0 <= y < 50
  //but we know of no connection between x and y.

}

//underspecififcation - we need to add more to the spec to prove that the code does what we want it to

method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures (m == x || m == y)
{
  s := x + y;
  if x <= y {
    m := y;
  } else {
    m := x;
  }
}

// A better specification
method MaxSum1(x: int, y: int) returns (s: int, m: int)
  requires true
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
{
  s := x + y;
  if x <= y {
    m := y;
  } else {
    m := x;
  }
}

method MaxSum01(x: int, y: int) returns (m: int)
  requires true
  ensures (m == x || m == y) && x <= m && y <= m
{
  // assert true;
  if x <= y
  { //assert x <= y && true;

    //assert (m == y || y == y) && x <= y && y <= y;
    m := y;
    //assert (m == x || m == y) && x <= m && y <= m;
  }
  else
  {
    //assert y < x && true;

    //assert (x == x || x == y) && x <= x && y <= x;
    m := x;
    //assert (m == x || m == y) && x <= m && y <= m;
  }
  //assert (m == x || m == y) && x <= m && y <= m;
}



method Test() {
  var s, m := MaxSum1(1928, 1);
  assert s == 1929 && m == 1928;
}



//Ghost code examples

method TripleN(x: int) returns (r: int)
  ensures r == 3*x
{
  var y := 2*x;
  r := x + y;
  ghost var a, b := DoubleQuadruple(x); // a and b are ghost variables and are assigned values by the ghost method
  assert a <= r <= b || b <= r <= a;
}

ghost method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2*x && b == 4*x
{
  a := 2*x;
  b := 2*a;
}

// functions are ghost by default, as client never sees them
function Average(a: int, b: int): int {
  (a + b) / 2 // function is a fact for reasoning
}

method Triple_with_functioncall(x: int) returns (r: int)
  requires x % 2 == 0
  ensures Average(r, 3*x) == 3*x
{
  var y;
  y:= x / 2;
  r := 6*y;
}



// while
// both guard and invariant are used to prove the correctness of the loop