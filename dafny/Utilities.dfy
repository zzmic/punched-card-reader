module UtilitiesModule {
  type arrayOfLength13<T> = a: array?<T> | a != null && a.Length == 13
    witness *

  type arrayOfLength12<T> = a: array?<T> | a != null && a.Length == 12
    witness *

  predicate IsAllTrue(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> arr[i] == true
  }

  predicate IsNotAllTrue(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    exists i :: 0 <= i < arr.Length && arr[i] == false
  }

  predicate IsAllFalse(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> arr[i] == false
  }

  predicate IsNotAllFalse(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    exists i :: 0 <= i < arr.Length && arr[i] == true
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
    exists i :: 0 <= i < prev.Length && (prev[i] == true && curr[i] == false )
  }
}
