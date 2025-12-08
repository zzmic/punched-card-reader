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

  method SeqToArr12<T>(s: seq<T>) returns (arr: arrayOfLength12<T>)
    requires |s| == 12
    ensures arr[..] == s[..]
    ensures fresh(arr)
  {
    // Reference: https://dafny.org/dafny/DafnyRef/DafnyRef#sec-array-allocation.
    arr := new T[12](i requires 0 <= i < 12 => s[i]);
  }

  method SeqToArr13<T>(s: seq<T>) returns (arr: arrayOfLength13<T>)
    requires |s| == 13
    ensures arr[..] == s[..]
    ensures fresh(arr)
  {
    arr := new T[13](i requires 0 <= i < 13 => s[i]);
  }
}
