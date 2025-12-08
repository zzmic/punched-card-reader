/**
  * Module containing utility types and functions.
  */
module UtilitiesModule {
  /**
    * Generic array types of length 13.
    */
  type arrayOfLength13<T> = a: array?<T> | a != null && a.Length == 13
    witness *

  /**
    * Generic array types of length 12.
    */
  type arrayOfLength12<T> = a: array?<T> | a != null && a.Length == 12
    witness *

  /**
    * Predicate to check if all elements in a boolean array are true.
    *
    * @param arr The boolean array to check.
    * @returns True if all elements are true, false otherwise.
    */
  predicate IsAllTrue(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> arr[i]
  }

  /**
    * Predicate to check if all elements in a boolean array are false.
    *
    * @param arr The boolean array to check.
    * @returns True if all elements are false, false otherwise.
    */
  predicate IsAllFalse(arr: array<bool>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> !arr[i]
  }

  /**
    * Predicate to check if all elements in an integer array are zero.
    *
    * @param arr The integer array to check.
    * @returns True if all elements are zero, false otherwise.
    */
  predicate IsAllZero(arr: array<int>)
    requires arr.Length >= 0
    reads arr
  {
    forall i :: 0 <= i < arr.Length ==> arr[i] == 0
  }

  /**
    * Predicate to check for a falling edge between two boolean arrays.
    *
    * @param prev The previous boolean array.
    * @param curr The current boolean array.
    * @returns True if there is at least one index where the value changed from true to false.
    */
  predicate IsFallingEdge(prev: array<bool>, curr: array<bool>)
    reads prev, curr
    requires prev.Length == curr.Length
  {
    exists i :: 0 <= i < prev.Length && (prev[i] && !curr[i])
  }

  /**
    * Method to convert a sequence of length 12 to an array of length 12.
    *
    * @param s The input sequence of length 12.
    * @returns An array of length 12 containing the elements of the sequence.
    */
  method SeqToArr12<T>(s: seq<T>) returns (arr: arrayOfLength12<T>)
    requires |s| == 12
    ensures arr[..] == s[..]
    ensures fresh(arr)
  {
    // Reference: https://dafny.org/dafny/DafnyRef/DafnyRef#sec-array-allocation.
    arr := new T[12](i requires 0 <= i < 12 => s[i]);
  }

  /**
    * Method to convert a sequence of length 13 to an array of length 13.
    *
    * @param s The input sequence of length 13.
    * @returns An array of length 13 containing the elements of the sequence.
    */
  method SeqToArr13<T>(s: seq<T>) returns (arr: arrayOfLength13<T>)
    requires |s| == 13
    ensures arr[..] == s[..]
    ensures fresh(arr)
  {
    arr := new T[13](i requires 0 <= i < 13 => s[i]);
  }
}
