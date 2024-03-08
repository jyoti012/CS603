// CA04 - dafny-02.html
// Q1. Rewrite your Max and Min methods

function MaxDef(a: int, b: int): int
{
  if a > b then a else b
}

function MinDef(a: int, b: int): int
{
  if a < b then a else b
}

method Min(a: int, b: int) returns (m: int)
  ensures m == MinDef(a, b) // using MinDef function
{
  if a > b {
    m := b;
  } else {
    m := a;
  }
}

method Max(a: int, b: int) returns (m: int)
  ensures m == MaxDef(a, b) // using MaxDef function
{
  if a > b {
    m := a;
  } else {
    m := b;
  }
}

method TestMinMax()
{
  var a := 3;
  var b := 5;
  var min := Min(a, b);
  var max := Max(a, b);
  assert min == 3;
  assert max == 5;
}

// recursive function that calculates the power of 2
function pow2(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * pow2(n - 1)
}

method TestPow2()
{
  var n := 3;
  var result := pow2(n);
  assert result == 8; // 2^3 = 8
}

// Q2. Generalized power function that calculate a^n
function pow(a: int, n: nat): int
{
  if n == 0 then
    1
  else
    a * pow(a, n - 1)
}

// Q3. Power function a^n
method Pow(a: int, n: nat) returns (result: int)
  // needs postcondition : added below
  requires n >= 0 // n should be a natural number
  ensures result == pow(a, n) // using pow function to calculate the result
{
  // todo : added result := 1;
  result := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    // needs another invariant : added
    invariant result * pow(a, (n-i)) == pow(a, n)
  {
    // todo : added result := result * a;
    result := result * a;
    i := i + 1;
  }
}

method TestPow()
{
  var a := 3;
  var n := 3;
  var result := Pow(a, n);
  assert result == 27; // 3^3 = 27
}

// Q4. Greatest common divisor
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b // decrease clause added
{
  if a == b then
    a
  else if b > a then
    gcd(b - a, a)
  else
    gcd(b, a - b)
}

method TestGcd()
{
  var a := 12;
  var b := 18;
  var result := gcd(a, b);
  assert result == 6; // 6 is the gcd of 12 and 18
}

// Q5. Binary search
predicate sorted(a: array<int>)
  reads a
{
  forall i, j | 0 <= i < j < a.Length :: a[i] <= a[j]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires sorted(a)
  ensures index == -1 || 0 <= index < a.Length
  ensures index == -1 ==> !exists index :: 0 <= index < a.Length && a[index] == value // there does not exist an index such that exists within the array and the value at that index is equal to the value
  ensures index >= 0  ==> a[index] == value // if the index is greater than or equal to 0, then the value at that index is equal to the value
{
  var low := 0;
  var high := a.Length;

  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant value !in a[..low] && value !in a[high..]
  {
    var mid := (high + low) / 2;

    if a[mid] < value {
      low := mid + 1;
    } else if a[mid] > value {
      high := mid;
    } else {
      return mid;
    }
  }
  index := -1;
}

// CA04 dafny-03.html

// Q1 Write a method that computes the sum of the first n natural numbers
method SumFirst(n: nat) returns (sum: nat)
  ensures sum == n * (n + 1) / 2
{
  // todo
  sum := 0;
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant sum == i * (i - 1) / 2
  {
    sum := sum + i;
    i := i + 1;
  }
}

method TestSumFirst()
{
  var n := 5;
  var sum := SumFirst(n);
  assert sum == 15; // 1 + 2 + 3 + 4 + 5 = 15
}

// Q2 Write a method which iteratively computes the nth Fibonacci number without any recursive calls and verify that it is equal to the mathematical definition

function Fib(n: nat): nat
{
  if n < 2 then n else Fib(n - 1) + Fib(n - 2)
}

method FibIter(n: nat) returns (x: nat)
  ensures x == Fib(n)
{
  if n == 0 { return 0; }
  var i := 1;
  var c := 1; 
  x := 1;
  while (i < n)
    invariant 0 < i <= n
    invariant c == Fib(i + 1)
    invariant x == Fib(i)
  {
    x, c := c, x + c;
    i := i + 1;
  }
}

method TestFibIter()
{
  var testUpTo := 2; 
  var n := 0;
  
  while n <= testUpTo
    decreases testUpTo - n 
  {
    var fibIterResult := FibIter(n);
    var fibResult := Fib(n);
    assert fibIterResult == fibResult; // assert that both methods return the same result for each n
    // Fibonacci numbers for n = 0, 1, 2 are 0, 1, 1 respectively
    if n == 0 {
      assert fibIterResult == 0;
      assert fibResult == 0;
    } else if n == 1 {
      assert fibIterResult == 1;
      assert fibResult == 1;
    } else if n == 2 {
      assert fibIterResult == 1;
      assert fibResult == 1;
    }
    n := n + 1; // incrementing n for the next iteration
  }
}

// Q3 Write and verify a method which finds the index pointing to the smallest element in an array.

method Smallest(a: array<int>) returns (minIndex: nat)
  requires 0 < a.Length
  ensures 0 <= minIndex < a.Length // minIndex should be a valid index
  ensures forall i :: 0 <= i < a.Length ==> a[minIndex] <= a[i] // minIndex points to the smallest element
{
  minIndex := 0; // assuming first element is the smallest
  var index := 1;
  while index < a.Length
    invariant 0 <= index <= a.Length // prevent index out of bounds
    invariant 0 <= minIndex < index // minIndex should be less than index 
    invariant forall i :: 0 <= i < index ==> a[minIndex] <= a[i] // current minIndex points to the smallest value checked
  {
    if a[index] < a[minIndex] {
      minIndex := index; // set minIndex to the current index if a smaller element is found
    }
    index := index + 1;
  }
}

method TestSmallest()
{
  var testArray := new int[5];
  testArray[0] := 5;
  testArray[1] := 3;
  testArray[2] := 4;
  testArray[3] := 1;
  testArray[4] := 2;

  var minIndex := Smallest(testArray);
  assert testArray[minIndex] == 1; // passes as 1 is the smallest element
  // assert testArray[minIndex] == 3; // fails as 3 is not the smallest element
  assert forall i :: 0 <= i < testArray.Length ==> testArray[minIndex] <= testArray[i];
}


// Q4 Write a method Filter which takes an array 'a' and a predicate 'P' as arguments, then builds a sequence of all
// the elements in 'a' satisfying P.

// unable to do this question

method Filter<T>(a: array<T>, P: T -> bool) returns (s: seq<T>)
{
  // todo
}
