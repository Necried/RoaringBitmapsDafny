include "../utils/Utils.dfy"
include "../utils/Bitvector.dfy"
include "../functional/Specification.dfy"
include "Conversion.dfy"

module RoaringBitmapBottom {
  import opened U = Utils
  import opened CS = ContainerSpecification
  import opened C = Conversion
  import opened RBU = RoaringBitsetUtils
  import opened BV64 = BitVec64

  method MkRoaringBitmapBottom(arrRb: array<bv64>, c: nat16) returns (rbb: RoaringBitmapBottom)
    requires arrRb.Length == 1024
    requires c >= 4096 && c == RBU.Cardinality(arrRb[..])
    ensures fresh(rbb)
    ensures rbb.Valid() && rbb.Elements == RoaringBitmapElements(arrRb[..])
  {
    rbb := new RoaringBitmapBottom.InitFromBitmaps(arrRb, c);
  }

  method ComputeCardinality(arrRb: array<bv64>) returns (c: nat16)
    requires arrRb.Length == 1024
    ensures c == RBU.Cardinality(arrRb[..])

  class RoaringBitmapBottom {
    var cardinality: nat
    var bmaps: array<bv64>
    ghost var Elements: Container
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      Repr == {this, bmaps} &&
      // There are exactly 1024 bv64's in the sequence
      bmaps.Length == 1024 &&
      // RoaringBitmap's cardinality is equal to number of set bits
      cardinality == RBU.Cardinality(bmaps[..]) &&
      // RoaringBitmap's cardinality must be greater than 4096
      4096 <= cardinality && // < Exp(2, 16) &&
      Elements.BitmapModel? &&
      Elements == RoaringBitmapElements(bmaps[..])
    }

    constructor InitFromBitmaps(bmapArg: array<bv64>, c: nat)
      requires bmapArg.Length == 1024
      requires c == RBU.Cardinality(bmapArg[..]) && c >= 4096
      ensures Valid()
      ensures Elements == RoaringBitmapElements(bmapArg[..])
      ensures fresh(Repr)
    {
      bmaps := new bv64[1024];
      new;
      CopyArray(bmapArg, bmaps);
      assert bmapArg[..] == bmaps[..];
      cardinality := c;
      Elements := RoaringBitmapElements(bmapArg[..]);
      Repr := {this, bmaps};
    }

    function In(x: nat16): bool
      requires Valid()
      reads Repr
      ensures In(x) == (InContainer(x, Elements))
    {
      var bmapIndex, bvecIndex := x / U.Exp(2, 6), x % U.Exp(2, 6);
      (bmaps[bmapIndex] & (1 << bvecIndex)) != 0
    }

    method {:axiom} Insert(x: nat16)
      requires Valid()
      modifies Repr
      ensures Valid() && Repr == old(Repr)
      ensures Elements == InsertContainer(x, old(Elements))
    {
      var (bmapIndex, bvIndex) := BvChunksFromElem(x);
      if !In(x) {
        bmaps[bmapIndex] := InsertBit(bmaps[bmapIndex], bvIndex);
        Elements := InsertContainer(x, Elements);
        cardinality := cardinality + 1;
        assume {:axiom} Elements == RoaringBitmapElements(bmaps[..]);
        assume {:axiom} cardinality == RBU.Cardinality(bmaps[..]);
      }
    }
  }
}