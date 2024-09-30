module Utils {

  type nat32 = n: int | 0 <= n < Exp(2, 32)
  type nat16 = n: int | 0 <= n < Exp(2, 16)

  datatype GhostOption<T> = ghost None | Some(value: T)


  function Exp(n: nat, e: nat): nat {
    if e == 0 then 1
    else n * Exp(n, e - 1)
  }

  function Sum(s: seq<nat>): nat {
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
  }

  method BinarySearch(a: array<nat16>, size: nat, key: nat) returns (n: nat)
    requires size <= a.Length
    requires forall i,j :: 0 <= i < j < size ==> a[i] < a[j]
    ensures 0 <= n <= size
    ensures forall i :: 0 <= i < n ==> a[i] < key
    ensures forall i :: n <= i < size ==> key <= a[i]
  {
    var lo, hi := 0, size;
    while lo < hi
      invariant 0 <= lo <= hi <= size
      invariant forall i :: 0 <= i < lo ==> a[i] < key
      invariant forall i :: hi <= i < size ==> key <= a[i]
    {
      var mid := (lo + hi) / 2;
      if a[mid] < key {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }
    n := lo;
  }

  method Contains(a: array<nat16>, size: nat, key: nat) returns (present: bool, n: nat)
    requires size <= a.Length
    requires forall i,j :: 0 <= i < j < size ==> a[i] < a[j]
    ensures present == exists i :: 0 <= i < size && key == a[i]
    ensures 0 <= n <= size
    ensures present ==> 0 <= n < size && key == a[n]
    ensures forall i :: 0 <= i < n ==> a[i] < key
    ensures forall i :: n < i < size ==> key < a[i]
    ensures !present ==> forall i :: n <= i < size ==> key < a[i]
  {
    n := BinarySearch(a, size, key);
    present := n < size && a[n] == key;
  }

  method BinarySearchSeq<T>(a: seq<T>, f: T -> nat, key: nat) returns (n: int)
    requires forall i,j :: 0 <= i < j < |a| ==> f(a[i]) <= f(a[j])
    ensures 0 <= n <= |a|
    ensures forall i :: 0 <= i < n ==> f(a[i]) < key
    ensures forall i :: n <= i < |a| ==> key <= f(a[i])
  {
    var lo, hi := 0, |a|;
    while lo < hi
      invariant 0 <= lo <= hi <= |a|
      invariant forall i :: 0 <= i < lo ==> f(a[i]) < key
      invariant forall i :: hi <= i < |a| ==> key <= f(a[i])
    {
      var mid := (lo + hi) / 2;
      if f(a[mid]) < key {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }
    n := lo;
  }

  function First<T1, T2>(t: (T1, T2)): T1 {
    t.0
  }

  function ContainsInSeq<T(==)>(s: seq<T>, key: T): bool {
    if s == [] then false
    else if s[0] == key then true
    else ContainsInSeq(s[1..], key)
  }

  function MapSeq<T1, T2>(f: T1 -> T2, s: seq<T1>): seq<T2> {
    if s == [] then []
    else [f(s[0])] + MapSeq(f, s[1..])
  }

  function UnionSeq<T>(seqSets: seq<set<T>>): set<T>
    ensures |seqSets| > 0 ==> UnionSeq(seqSets) == seqSets[0] + UnionSeq(seqSets[1..])
  {
    if seqSets == [] then {}
    else seqSets[0] + UnionSeq(seqSets[1..])
  }

  function Compose<A, B, C>(f: A -> B, g: B -> C): A -> C {
    x => g(f(x))
  }

  function ComplementBv64(bv: bv64): bv64 {
    !bv
  }

  method InsertAtArrayIndex(arr: array<nat16>, curLength: nat, elem: nat16, index: nat)
    requires 0 <= index <= curLength < arr.Length
    requires forall i, j :: 0 <= i < j < curLength ==> arr[i] < arr[j]
    requires forall i :: 0 <= i < index ==> arr[i] < elem
    requires forall i :: index <= i < curLength ==> elem < arr[i]
    modifies arr
    ensures arr[0..index] == old(arr[0..index])
    ensures arr[index+1..curLength+1] == old(arr[index..curLength])
    ensures arr[..curLength+1] == old(arr[0..index]) + [elem] + old(arr[index..curLength])
    ensures arr[index] == elem
    ensures forall i :: 0 <= i < index ==> arr[i] <= elem
    ensures forall i :: index + 1 <= i < curLength + 1 ==> elem < arr[i]
    ensures forall i, j :: 0 <= i < j < curLength + 1 ==> arr[i] < arr[j]
  {
    ghost var resSeq := arr[0..index] + [elem] + arr[index..curLength];
    assert resSeq[0..index] == old(arr[0..index]);
    assert resSeq[index..curLength+1] == [elem] + old(arr[index..curLength]);
    var n := curLength + 1;
    while n > 0
      invariant 0 <= n <= curLength + 1
      invariant |resSeq| == curLength + 1
      invariant forall i :: 0 <= i < n ==> arr[i] == old(arr[i])
      invariant forall i :: n <= i <= curLength ==> arr[i] == resSeq[i]
    {
      n := n - 1;
      if n == index {
        arr[n] := elem;
        assert arr[index..curLength] == resSeq[index..curLength];
      } else if n > index {
        arr[n] := arr[n - 1];
      } else {
        assert n < index;
        assert arr[n] == old(arr[n]);
      }
    }
  }

  method InsertInRoaringSortedArray<T>(arr: array<(nat, T)>, curLength: nat, elem: (nat, T), index: nat)
    requires 0 <= index <= curLength < arr.Length
    requires forall i, j :: 0 <= i < j < curLength ==> arr[i].0 <= arr[j].0
    requires forall i :: 0 <= i < index ==> arr[i].0 <= elem.0
    requires forall i :: index <= i < curLength ==> elem.0 < arr[i].0
    modifies arr
    ensures arr[0..index] == old(arr[0..index])
    ensures arr[..curLength+1] == old(arr[0..index]) + [elem] + old(arr[index..curLength])
    ensures arr[index] == elem
    ensures forall i :: 0 <= i < index ==> arr[i].0 <= elem.0
    ensures forall i :: index + 1 <= i < curLength + 1 ==> elem.0 < arr[i].0
    ensures forall i, j :: 0 <= i < j < curLength ==> arr[i].0 <= arr[j].0
  {
    ghost var resSeq := arr[0..index] + [elem] + arr[index..curLength];
    assert resSeq[0..index] == old(arr[0..index]);
    assert resSeq[index..curLength+1] == [elem] + old(arr[index..curLength]);
    var n := curLength + 1;
    while n > 0
      invariant 0 <= n <= curLength + 1
      invariant |resSeq| == curLength + 1
      invariant forall i :: 0 <= i < n ==> arr[i] == old(arr[i])
      invariant forall i :: n <= i <= curLength ==> arr[i] == resSeq[i]
    {
      n := n - 1;
      if n == index {
        arr[n] := elem;
        assert arr[index..curLength] == resSeq[index..curLength];
      } else if n > index {
        arr[n] := arr[n - 1];
      } else {
        assert n < index;
        assert arr[n] == old(arr[n]);
      }
    }
  }

  predicate Trichotomy(a: bool, b: bool, c: bool) {
    (a || b || c) && (a == b == c)
  }

  function Sum2(f: int ~> real, lo: int, hi: int): real
    requires lo <= hi
    requires forall i :: f.requires(i)
    reads f.reads
    decreases hi - lo
  {
    if lo == hi then 0.0 else
    f(lo) + Sum2(f, lo + 1, hi)
  }

  function TestSeq(): set<nat> {
    var x := UnionSeq(MapSeq(x => (if x < 2 then {x} else {x + 1}), [0, 1, 2, 3, 4]));
    assert x == {0, 1, 3, 4, 5};
    x
  }

  lemma SeqAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures (a + b) + c == a + (b + c)
  {

  }

  function Max(a: nat, b: nat): nat

  {
    if a > b then a else b
  }

  method CopyArray(src: array, dst: array)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == old(src[i])
  {
    forall i | 0 <= i < src.Length {
      dst[i] := src[i];
    }
  }

  function Min(a: nat, b: nat): nat {
    if a < b then a else b
  }


  function ElemFromChunks(topChunk: nat16, botChunk: nat16): nat32 {
    topChunk * Exp(2, 16) + botChunk
  }

  function ChunksFromElem(elem: nat32): (nat16, nat16)
  {
    (elem / Exp(2, 16), elem % Exp(2, 16))
  }
}