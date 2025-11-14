module CommonTypesModule {
  type array_13<T> = a: array?<T> | a != null && a.Length == 13
    witness *

  type array_12<T> = a: array?<T> | a != null && a.Length == 12
    witness *

  predicate IsAllFalse(arr : array<bool>)
    reads arr
    requires arr.Length >= 0
  {
    forall i :: 0 <= i < arr.Length ==> (arr[i] == false)
  }

  predicate IsAllTrue(arr : array<bool>)
    reads arr
    requires arr.Length >= 0
  {
    forall i :: 0 <= i < arr.Length ==> (arr[i] == true)
  }

  predicate IsFallingEdge(prev : array<bool>, curr : array<bool>)
    reads prev, curr
    requires prev.Length == curr.Length
  {
    exists i :: 0 <= i < prev.Length && (prev[i] == true && curr[i] == false )
  }
}
