module UtilitiesModule {
  type arrayOfLength13<T> = a: array?<T> | a != null && a.Length == 13
    witness *

  type arrayOfLength12<T> = a: array?<T> | a != null && a.Length == 12
    witness *

  predicate IsAllTrue(arr: array<bool>)
    reads arr
    requires arr.Length >= 0
    ensures IsAllTrue(arr) <==> forall i :: 0 <= i < arr.Length ==> arr[i] == true
  {
    forall i :: 0 <= i < arr.Length ==> (arr[i] == true)
  }

  predicate IsAllFalse(arr: array<bool>)
    reads arr
    requires arr.Length >= 0
    ensures IsAllFalse(arr) <==> forall i :: 0 <= i < arr.Length ==> arr[i] == false
  {
    forall i :: 0 <= i < arr.Length ==> (arr[i] == false)
  }

  predicate IsAllZero(arr: array<int>)
    reads arr
    requires arr.Length >= 0
  {
    forall i :: 0 <= i < arr.Length ==> (arr[i] == 0)
  }

  predicate IsFallingEdge(prev: array<bool>, curr: array<bool>)
    reads prev, curr
    requires prev.Length == curr.Length
  {
    exists i :: 0 <= i < prev.Length && (prev[i] == true && curr[i] == false )
  }

  method SeqToArray13_Bool(s: seq<bool>) returns (arr: arrayOfLength13<bool>)
    requires |s| == 13
    ensures arr.Length == 13
    ensures forall i :: 0 <= i < 13 ==> arr[i] == s[i]
  {
    arr := new bool[13](_ => false);
    var i := 0;
    while i < 13
      modifies arr
      invariant 0 <= i <= 13
      invariant forall j :: 0 <= j < i ==> arr[j] == s[j]
    {
      arr[i] := s[i];
      i := i + 1;
    }
  }

  method SeqToArray12_Bool(s: seq<bool>) returns (arr: arrayOfLength12<bool>)
    requires |s| == 12
    ensures arr.Length == 12
    ensures forall i :: 0 <= i < 12 ==> arr[i] == s[i]
  {
    arr := new bool[12](_ => false);
    var i := 0;
    while i < 12
      modifies arr
      invariant 0 <= i <= 12
      invariant forall j :: 0 <= j < i ==> arr[j] == s[j]
    {
      arr[i] := s[i];
      i := i + 1;
    }
  }

  method GetColumnOutputFromPrevPunched(prev_punched: arrayOfLength13<bool>) returns (res: arrayOfLength12<bool>)
    requires prev_punched.Length == 13
    ensures forall i :: 0 <= i < 12 ==> res[i] == prev_punched[i+1]
  {
    res := new bool[12](_ => false);
    var i := 0;
    while i < 12
      modifies res
      invariant 0 <= i <= 12
      invariant forall j :: 0 <= j < i ==> res[j] == prev_punched[j+1]
    {
      res[i] := prev_punched[i+1];
      i := i + 1;
    }
    return res;
  }
}
