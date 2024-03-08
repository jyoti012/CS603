// what is the purpose of the function
// Purpose of the function is to return the absolute value of the input number

// method Abs(n: int) returns (result: int)
//     ensures result >= 0 
//     ensures result == n || result == -n  
// {
//     if n < 0 {
//         result := -n;
//     } else {
//         result := n;
//     }
// }

method Abs(x: int) returns (result: int)
    requires -10 < x < 10
    ensures result >= 0  // ✓ succeeds
{
    if x < 0 {
        result := -x;
    } else {
        result := x;
    }
}

method {:main} TestAbs()
{
    var x := Abs(-3);
    // assert x == 3;
    assert x >= 0;  // ✗ fails
    print x, "\n";
}