include "../functional/Specification.dfy"
include "../utils/Utils.dfy"
include "../utils/Permutations.dfy"
include "../utils/CollectionHelpers.dfy"
include "../utils/Bitvector.dfy"

module Conversion {
  import C = ContainerSpecification
  import CH = CollectionHelpers
  import P = Permutations
  import opened U = Utils
  import BV = BitVec64
  import RBU = RoaringBitsetUtils

  ghost function RoaringArrayElements(seqElems: seq<nat16>): C.Container 
    requires |seqElems| <= 4096
    requires forall i, j :: 0 <= i < j < |seqElems| ==> seqElems[i] < seqElems[j]
    ensures var c := RoaringArrayElements(seqElems);
      c.ArrayModel? && C.Valid(c)
  {
    var setElems := set i | i in seqElems;
    UniqueSeqToSetPreservesCardinality(seqElems, setElems);
    C.ArrayModel(setElems)
  }

  lemma UniqueSeqToSetPreservesCardinality(seqElems: seq<int>, setElems: set<int>)
    requires P.NoDuplicateSeq(seqElems)
    requires setElems == (set i | i in seqElems)
    ensures |seqElems| == |setElems|
  {
    if |seqElems| == 0 {
      assert |setElems| == 0;
    } else {
      var i :| 0 <= i < |seqElems|;
      var n :| n in setElems && seqElems[i] == n;
      var seqCut := seqElems[..i] + seqElems[i+1..];
      UniqueSeqToSetPreservesCardinality(seqCut, setElems - {n});
    }
  }

  ghost function {:axiom} RoaringBitmapElements(bmapParam: seq<bv64>): C.Container
    requires |bmapParam| == 1024
    ensures var outputSet := RoaringBitmapElements(bmapParam);
            outputSet.BitmapModel? &&
            C.Valid(outputSet) && RBU.Repr(bmapParam, outputSet.elems)
            
  ghost function {:axiom} RoaringBitmapElementsUpTo(bmapParam: array<bv64>, i: nat16): set<nat16>
    requires bmapParam.Length == 1024
    ensures var outputSet := RoaringBitmapElementsUpTo(bmapParam, i);
      RBU.ReprUpTo(bmapParam[..], outputSet, i)

  method {:vcs_split_on_every_assert} {:axiom} ConvertBitmapToArray(bmap: array<bv64>) returns (arr: array<nat16>)
    requires bmap.Length == 1024
    requires RBU.Cardinality(bmap[..]) < 4096
    ensures fresh(arr) && arr.Length == 4096
    ensures forall i, j :: 0 <= i < j < RBU.Cardinality(bmap[..]) ==> arr[i] < arr[j]
    ensures C.Valid(RoaringArrayElements(arr[..RBU.Cardinality(bmap[..])]))
    ensures RoaringArrayElements(arr[..RBU.Cardinality(bmap[..])]) == 
           RoaringBitmapElements(bmap[..])
  {
    arr := new nat16[4096];
    var bmapIndex := 0;
    var arrIndex := 0;
    ghost var containerBmap := RoaringBitmapElements(bmap[..]);
    // This is in the precondition but makes the verifier much faster if it's stated
    assert RBU.Cardinality(bmap[..]) < 4096;
    // This says that the cardinality of the intermediate construction
    // is strictly increasing on each iteration of the loop
    RBU.CardinalityIncreasing(bmap[..], 1024);
    // This states that taking the cardinality of bitmaps up to the max index is
    // equal to the cardinality of the whole bitmap
    RBU.CardinalityTo1024(bmap[..]);
    while bmapIndex < 1024
      invariant 0 <= bmapIndex <= 1024
      invariant arrIndex == RBU.CardinalityTo(bmap[..], bmapIndex)
      // invariant RoaringBitmapElementsUpTo(bmap, bmapIndex * 64) == 
      //          C.Elements(RoaringArrayElements(arr, arrIndex))
      invariant forall k :: 0 <= k < arrIndex - 1 ==> arr[k] < arr[k+1]
    {
      // This states that each loop computes the Popcnt of the current bitmap `w`
      RBU.CardinalitySplitLast(bmap[..], bmapIndex);
      var w := bmap[bmapIndex];
      while w != 0
        invariant w >= 0
        invariant arrIndex + BV.Popcnt(w) == RBU.CardinalityTo(bmap[..], bmapIndex + 1)
        invariant forall k :: 0 <= k < arrIndex - 1 ==> arr[k] < arr[k+1]
        decreases w
      {
        // Use the following formula to isolate the rightmost 1-bit, producing 0 if none (e.g., 01011000 ⇒ 00001000):
        // BV.IsolateRightmostBit(w);
        // BV.SingletonRightmostBitIndex(w);
        var t := w & (-w);
        // This two lines ensures that the assignment to arr[arrIndex] is always a nat16
        BV.PopcntLessThan64(t - 1);
        assert BV.Popcnt(t - 1) < 64;
        assert bmapIndex + 1 <= 1024;
        assert forall n :: n < 64 ==> 1024 * n < Exp(2, 16);
        // Subtraction `t - 1` occurs on a power of two, thereby giving the index of the bit with Popcnt
        var elem := BV.Popcnt(t - 1) * (bmapIndex + 1);
        arr[arrIndex] := elem;
        assume {:axiom} RBU.BvGetBit(bmap[..], arr[arrIndex]);
        // We know that the elements are increasing; this is currently baked in as an assumption
        assume {:axiom} arrIndex > 0 ==> arr[arrIndex] > arr[arrIndex - 1];
        assert forall k :: 0 <= k < arrIndex - 1 ==> arr[k] < arr[k+1];
        // Drops the rightmost bit
        assert BV.Popcnt(w) == BV.Popcnt(w & (w - 1)) + 1;
        w := w & (w - 1);
        arrIndex := arrIndex + 1;
      }
      // This assertion seems to be needed to remind Dafny of the invariant
      assert forall k :: 0 <= k < arrIndex - 1 ==> arr[k] < arr[k+1];
      bmapIndex := bmapIndex + 1;
    }
    SortedTransitiveForall(arr, arrIndex);
    assume {:axiom} RoaringArrayElements(arr[..RBU.Cardinality(bmap[..])]) == 
           RoaringBitmapElements(bmap[..]);
  }

/*
    requires bmap.Length == 1024
    requires RBU.Cardinality(bmap) < 4096
    ensures fresh(arr) && arr.Length == 4096 &&
      (forall i, j :: 0 <= i < j < RBU.Cardinality(bmap) ==> arr[i] < arr[j]) &&
      C.Valid(RoaringArrayElements(arr, RBU.Cardinality(bmap)))
*/

  method ConvertArrayToBitmap(arr: array<nat16>) returns (bmap: array<bv64>)
    requires arr.Length == 4096
    requires forall i, j :: 0 <= i < j < 4096 ==> arr[i] < arr[j]
    ensures fresh(bmap) && bmap.Length == 1024
    ensures C.Valid(RoaringBitmapElements(bmap[..]))
    ensures RoaringBitmapElements(bmap[..]).elems == RoaringArrayElements(arr[..4096]).elems
  {
    bmap := new bv64[1024];
    var c := 0;
    var n := 0;
    while n != arr.Length
      invariant 0 <= n <= arr.Length
      invariant bmap.Length == 1024
      invariant forall i :: 0 <= i < n ==>
        var (bmapIndex, bvIndex) := RBU.BvChunksFromElem(arr[i]);
        arr[i] < U.Exp(2, 16) && bmap[bmapIndex] & (1 << bvIndex) != 0
      invariant fresh(bmap)
    {
      var (bmapIndex, bvIndex) := RBU.BvChunksFromElem(arr[n]);
      bmap[bmapIndex] := bmap[bmapIndex] | (1 << bvIndex);
      n := n + 1;
    }
    assume {:axiom} RoaringBitmapElements(bmap[..]).elems == RoaringArrayElements(arr[..4096]).elems;
  }

  lemma SortedTransitive(a: array<nat16>, i: nat, j: nat, arrLength: nat)
    requires arrLength <= a.Length
    requires forall k :: 0 <= k < arrLength - 1 ==> a[k] < a[k+1]
    requires 0 <= i < j < arrLength
    ensures a[i] < a[j]
  {
    if i == j {

    } else {
      var k := i;
      while k < j
        invariant i <= k <= j
        invariant a[i] < a[k] || i == k
      {
        k := k + 1;
        assert a[k-1] < a[k];
        assert a[i] < a[k];
      }
    }
  }

  lemma SortedTransitiveForall(a: array<nat16>, arrLength: nat)
    requires arrLength <= a.Length
    requires forall k :: 0 <= k < arrLength - 1 ==> a[k] < a[k+1]
    ensures forall i, j :: 0 <= i < j < arrLength ==> a[i] < a[j]
  {
    // This loop goes through every pair (i, j) and applies the SortedTransitive lemma
    forall i, j | 0 <= i < j < arrLength
    ensures a[i] < a[j]
    {
      SortedTransitive(a, i, j, arrLength);
    }
  }
}