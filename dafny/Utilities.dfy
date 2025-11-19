module UtilitiesModule {
  type arrayOfLength13<T> = a: array?<T> | a != null && a.Length == 13
    witness *

  type arrayOfLength12<T> = a: array?<T> | a != null && a.Length == 12
    witness *

  predicate IsAllTrue(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> arr[i]
  }

  predicate IsAllFalse(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> !arr[i]
  }

  predicate IsAllZero(arr: array<int>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> arr[i] == 0
  }

  predicate IsFallingEdge(prev: array<bool>, curr: array<bool>)
    reads prev, curr
    requires prev.Length == curr.Length
  {
    exists i :: 0 <= i < prev.Length && (prev[i] && !curr[i])
  }

  // Generalizing the method to work for any type `T` triggers the
  // "unless an initializer is provided for the array elements, a new array of 'T' must have empty size" error.
  method SeqToArr12_bool(s: seq<bool>) returns (arr: arrayOfLength12<bool>)
    requires |s| == 12
    ensures arr[..] == s[..]
  {
    arr := new bool[12];
    var i: int := 0;
    while i < 12
      invariant 0 <= i <= 12
      invariant forall j :: 0 <= j < i ==> arr[j] == s[j]
    {
      arr[i] := s[i];
      i := i + 1;
    }
  }

  method SeqToArr13_int(s: seq<int>) returns (arr: arrayOfLength13<int>)
    requires |s| == 13
    ensures arr[..] == s[..]
  {
    arr := new int[13];
    var i: int := 0;
    while i < 13
      invariant 0 <= i <= 13
      invariant forall j :: 0 <= j < i ==> arr[j] == s[j]
    {
      arr[i] := s[i];
      i := i + 1;
    }
  }

  method SeqToArr13_bool(s: seq<bool>) returns (arr: arrayOfLength13<bool>)
    requires |s| == 13
    ensures arr[..] == s[..]
  {
    arr := new bool[13];
    var i: int := 0;
    while i < 13
      invariant 0 <= i <= 13
      invariant forall j :: 0 <= j < i ==> arr[j] == s[j]
    {
      arr[i] := s[i];
      i := i + 1;
    }
  }
}
