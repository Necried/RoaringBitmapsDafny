include "Utils.dfy"

module BitVec64 {
  import U = Utils

  type fin64 = x: int | 0 <= x < 64

  predicate GetBit(bs: bv64, k: fin64) {
    (bs >> k) & 1 == 1
  }

  predicate Repr(bs: bv64, s: set<fin64>) {
    s == set x: fin64 | GetBit(bs, x)
  }

  lemma {:axiom} GetRepr(bs: bv64, s: set<fin64>)
    requires Repr(bs, s)
    ensures forall k :: GetBit(bs, k) == (k in s)

  function InsertBit(bs: bv64, k: fin64): bv64 {
    bs | (1 << k)
  }

  lemma {:axiom} InsertRepr(bs: bv64, s: set<fin64>, k: fin64)
    requires Repr(bs, s)
    ensures Repr(InsertBit(bs, k), {k} + s)

  function Popcnt(bv: bv64): nat
  {
    if bv == 0
    then 0
    else
      1 + Popcnt(bv & (bv - 1))
  }

  lemma {:axiom} PopcntLessThanEq64(bv: bv64)
    ensures Popcnt(bv) <= 64

  lemma {:axiom} PopcntLessThan64(bv: bv64)
    requires bv != U.Exp(2, 16) as bv64
    ensures Popcnt(bv) < 64

  lemma {:axiom} CardinalityRepr(bv: bv64, s: set<fin64>)
    requires Repr(bv, s)
    ensures |s| == Popcnt(bv)

  lemma {:axiom} DropRightmostBit(bv: bv64)
    ensures Popcnt(bv & (bv - 1)) + 1 == Popcnt(bv)

  function RightmostBitIndex(bv: bv64): fin64
    requires bv != 0
    ensures var n := RightmostBitIndex(bv);
            GetBit(bv, n) &&
            forall i :: 0 <= i < n ==> !GetBit(bv, i)

  lemma ZeroRightShift(bv: bv64)
    requires bv & 1 == 0
    ensures var bvShr1 := bv >> 1;
            bv == bvShr1 << 1
  {

  }

  lemma {:noverify} ExistsRightmostBit(bv: bv64)
    requires bv != 0
    ensures exists n :: 0 <= n < 64 && GetBit(bv, n) &&
                        forall i :: 0 <= i < n ==> !GetBit(bv, i)
  {
    if GetBit(bv, 0) {

    } else {
      assert !GetBit(bv, 0);
      var bvShl := bv >> 1;
      ExistsRightmostBit(bvShl);
      var n :| 0 <= n < 63 && GetBit(bvShl, n) &&
               forall i :: 0 <= i < n ==> !GetBit(bvShl, i);
      assume {:axiom} GetBit(bvShl, n) == GetBit(bv, n + 1);
    }
  }

  function SingletonBitSet(n: fin64): bv64
    requires n < 64
    ensures var bv := SingletonBitSet(n);
            GetBit(bv, n) &&
            forall i: fin64 :: i != n ==> !GetBit(bv, i)
  {
    1 << n
  }

  lemma {:axiom} IsolateRightmostBit(bv: bv64)
    requires bv != 0
    ensures exists n :: 0 <= n < 64 &&
                        bv & (-bv) == SingletonBitSet(n)

  lemma {:axiom} SingletonRightmostBitIndex(bv: bv64)
    requires bv != 0
    ensures
      var t := bv & (-bv);
      var idx := Popcnt(t - 1);
      idx == RightmostBitIndex(bv)
}

module RoaringBitsetUtils {
  import opened BitVec64
  import opened Utils

  type rbv = bv: seq<bv64> | |bv| == 1024 witness *
  type fin1024 = x: int | 0 <= x < 1024

  function BvChunksFromElem(n: nat16): (fin1024, fin64) {
    (n / 64, n % 64)
  }

  predicate BvGetBit(b: rbv, k: nat16)
  {
    var (topIndex, bvIndex) := BvChunksFromElem(k);
    GetBit(b[topIndex], bvIndex)
  }

  predicate Repr(b: rbv, s: set<nat16>)
  {
    s == set x: nat16 | BvGetBit(b, x)
  }

  predicate ReprUpTo(b: rbv, s: set<nat16>, n: nat16)
  {
    s == set x: nat16 | x <= n && BvGetBit(b, x)
  }

  lemma ReprUpToNat16(b: rbv, s: set<nat16>)
    ensures Repr(b, s) == ReprUpTo(b, s, Exp(2, 16) - 1)
  {

  }

  ghost function Cardinality(b: rbv): nat
  {
    CardinalitySeq(b)
  }

  ghost function CardinalitySeq(b: seq<bv64>): nat
  {
    if b == [] then 0
    else Popcnt(b[0]) + CardinalitySeq(b[1..])
  }

  ghost function CardinalityTo(b: rbv, k: nat): nat
    requires 0 <= k <= 1024
  {
    CardinalitySeq(b[..k])
  }

  lemma CardinalityTo1024(b: rbv)
    ensures Cardinality(b) == CardinalityTo(b, 1024)
  {
    assert b[..] == b[..1024];
  }

  lemma CardinalitySplit(b1: seq<bv64>, b2: seq<bv64>)
    ensures CardinalitySeq(b1 + b2) == CardinalitySeq(b1) + CardinalitySeq(b2)
  {
    if b1 == [] {
      calc {
        CardinalitySeq([] + b2);
      =={ assert [] + b2 == b2; }
        CardinalitySeq(b2);
      ==
        CardinalitySeq([]) + CardinalitySeq(b2);
      }
    } else {
      calc {
        CardinalitySeq(b1) +  CardinalitySeq(b2);
      ==
        Popcnt(b1[0]) + CardinalitySeq(b1[1..]) +  CardinalitySeq(b2);
      =={ CardinalitySplit(b1[1..], b2); }
        Popcnt(b1[0]) + CardinalitySeq(b1[1..] + b2);
      =={ assert b1[1..] + b2 == (b1 + b2)[1..]; }
        Popcnt((b1 + b2)[0]) + CardinalitySeq((b1 + b2)[1..]);
      ==
        CardinalitySeq(b1 + b2);
      }
    }
  }

  lemma CardinalitySplitLast(b: rbv, k: nat)
    requires k < 1024
    ensures CardinalityTo(b, k + 1) == CardinalityTo(b, k) + Popcnt(b[k])
  {
    if k == 0 {
      assert CardinalityTo(b, 1) == CardinalitySeq(b[..1]);
    } else {
      calc {
        CardinalityTo(b, k + 1);
      ==
        CardinalitySeq(b[..k+1]);
      =={ assert b[..k+1] == b[..k] + [b[k]]; }
        CardinalitySeq(b[..k] + [b[k]]);
      =={ CardinalitySplit(b[..k], [b[k]]); }
        CardinalitySeq(b[..k]) + CardinalitySeq([b[k]]);
      ==
        CardinalityTo(b, k) + Popcnt(b[k]);
      }
      assert CardinalityTo(b, k + 1) == CardinalityTo(b, k) + Popcnt(b[k]);
    }
  }


  // Universal introduction: https://stackoverflow.com/questions/63383653/how-to-prove-universal-introduction-in-dafny
  lemma CardinalityIncreasing(b: rbv, k: nat)
    requires k <= 1024
    ensures forall i :: 0 <= i <= k ==>
                          CardinalityTo(b, k) >= CardinalityTo(b, i)
  {
    if k == 0 {
    } else {
      forall i: nat | 0 <= i <= k
        ensures CardinalityTo(b, k) >= CardinalityTo(b, i)
      {
        if i == k {
        } else {
          assert i < k;
          calc >= {
            CardinalityTo(b, k);
          ==
            CardinalitySeq(b[..k]);
          =={ CardinalitySplit(b[..i], b[i..k]);
              assert b[..i] + b[i..k] == b[..k]; }
            CardinalitySeq(b[..i]) + CardinalitySeq(b[i..k]);
          >=
            CardinalitySeq(b[..i]);
          }
        }
      }
    }
  }
}

method Test() {
  var b: bv4 := 5;
  assert (-b) == 11;
  assert b & (-b) == 1;
  assert b & (b - 1) == 4;

  var b2: bv4 := 4;
  assert b2 & (-b2) == 4;
  assert b2 & (b2 - 1) == 0;
}