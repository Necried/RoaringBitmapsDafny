include "../utils/Utils.dfy"
include "../functional/Specification.dfy"
include "Conversion.dfy"
include "RoaringArrayContainer.dfy"
include "RoaringBitmapContainer.dfy"
include "../utils/Bitvector.dfy"

module RoaringContainer {
  import opened U = Utils
  import CS = ContainerSpecification
  import C = Conversion
  import opened RBU = RoaringBitsetUtils
  import opened BV64 = BitVec64

  datatype RoaringContainerObject
    = RoaringArray(arr: array<nat16>, cardinality: nat16)
    | RoaringBitmap(bmap: array<bv64>, cardinality: nat16)

  ghost function ObjectFrame(r: RoaringContainerObject): object
  {
    match r
    case RoaringArray(arr, _) => arr
    case RoaringBitmap(bmap, _) => bmap
  }

  ghost predicate Valid(r: RoaringContainerObject)
    reads ObjectFrame(r)
  {
    match r
    case RoaringArray(arr, c) =>
      c <= 4096 && ValidRoaringArray(arr, c)
    case RoaringBitmap(bmaps, c) =>
      c >= 4096 && ValidRoaringBitmap(bmaps, c)
  }

  ghost predicate ValidRoaringArray(arr: array<nat16>, c: nat16) 
    reads arr
  {
    // RoaringArray's cardinality is equal to length of its elems
    arr.Length == 4096 &&
    // RoaringArray's cardinality cannot exceed 4096
    c <= arr.Length &&
    // RoaringArray elements are sorted
    (forall i,j :: 0 <= i < j < c ==> arr[i] < arr[j]) &&
    // RoaringArrayElements convert `elems` into a set
    CS.Valid(C.RoaringArrayElements(arr[..c]))
  }
  ghost predicate ValidRoaringBitmap(bmaps: array<bv64>, c: nat16)
    reads bmaps
  {
    bmaps.Length == 1024 &&
    // RoaringBitmap's cardinality is equal to number of set bits
    c == RBU.Cardinality(bmaps[..]) &&
    // RoaringBitmap's cardinality must be greater than 4096
    c >= 4096 &&
    CS.Valid(C.RoaringBitmapElements(bmaps[..]))
  }
  
  ghost function Elements(r: RoaringContainerObject): CS.Container
    reads ObjectFrame(r)
    requires Valid(r)
  {
    match r
    case RoaringArray(arr, c) => C.RoaringArrayElements(arr[..c])
    case RoaringBitmap(bmaps, c) => C.RoaringBitmapElements(bmaps[..])
  }

  method In(x: nat16, r: RoaringContainerObject) returns (present: bool)
    requires Valid(r)
    ensures present == CS.InContainer(x, Elements(r))
  {
    match r
    case RoaringArray(arr, c) =>
      var isPresent, foundIndex := Contains(arr, c, x);
      present := isPresent;
    case RoaringBitmap(bmaps, c) =>
      var bmapIndex, bvecIndex := x / U.Exp(2, 6), x % U.Exp(2, 6);
      present := (bmaps[bmapIndex] & (1 << bvecIndex)) != 0;
  }

  method Insert(x: nat16, r: RoaringContainerObject) returns (r': RoaringContainerObject)
    requires Valid(r)
    modifies ObjectFrame(r)
    ensures Valid(r')
    ensures Elements(r') == CS.InsertContainer(x, Elements(r'))
  {
    match r
    case RoaringArray(arr, c) =>
      assume c < 4096;
      var xIsPresent := InsertArray(x, arr, c);
      r' := RoaringArray(arr, if xIsPresent then c else c + 1);
    case RoaringBitmap => assume false;
  }
  method InsertArray(x: nat16, arr: array<nat16>, cardinality: nat16) returns (isPresent: bool)
    requires ValidRoaringArray(arr, cardinality) && cardinality < 4096
    modifies arr
    ensures ValidRoaringArray(arr, cardinality)
    ensures 
      !isPresent ==> 
        && forall i, j :: 0 <= i < j < cardinality + 1 ==> arr[i] < arr[j]
        && CS.InContainer(x, C.RoaringArrayElements(arr[..cardinality + 1]))
  {
    var present, insertIndex := Contains(arr, cardinality, x);
    isPresent := present;
    if !isPresent {
      assert !CS.InContainer(x, Elements(RoaringArray(arr, cardinality)));
      assert x !in arr[..cardinality];
      InsertAtArrayIndex(arr, cardinality, x, insertIndex);
      // cardinality' := cardinality + 1;
      assert arr[..cardinality] == arr[0..insertIndex] + arr[insertIndex..cardinality];
      assert x in arr[..cardinality + 1];
      assert forall i, j :: 0 <= i < j < cardinality + 1 ==>
        arr[i] < arr[j];
      assert CS.InContainer(x, C.RoaringArrayElements(arr[..cardinality + 1]));
    } else {
      assert x in arr[..cardinality];
      assert CS.InContainer(x, Elements(RoaringArray(arr, cardinality)));
    }
  }

  method InsertBitmap(x: nat16, bmaps: array<bv64>, cardinality: nat16)
    returns (bmaps': array<bv64>, cardinality': nat16)
    requires ValidRoaringBitmap(bmaps, cardinality) && cardinality >= 4096
    ensures cardinality' <= 4096
    ensures ValidRoaringBitmap(bmaps', cardinality')
    ensures Elements(RoaringBitmap(bmaps', cardinality')) == 
            CS.InsertContainer(x, Elements(RoaringBitmap(bmaps, cardinality)))

}

module RoaringBitmap {
  import opened U = Utils
  import C = Conversion
  import RBS = RoaringBitmapSpecification
  import CS = ContainerSpecification
  import BV = BitVec64
  import RBU = RoaringBitsetUtils
  import opened RC = RoaringContainer

  class {:autocontracts} RBitmap {
    ghost var Repr: set<object>
    ghost var model: RBS.RBitmapModel

    var topChunks: array<nat16>
    var containers: array<GhostOption<RoaringContainerObject>>
    var size: nat16

    ghost predicate Valid()
    {
      containers in Repr &&
      topChunks.Length == containers.Length == U.Exp(2, 16) &&
      size <= topChunks.Length && size <= containers.Length && size == |model| &&

      // The underlying model is valid
      RBS.Valid(model) &&

      // Top-level indices corresponds to the model's topChunks
      topChunks[..size] == RBS.TopChunks(model) &&

     (forall i :: 0 <= i < size ==> 
       var c := containers[topChunks[i]];
       c != None &&
       ObjectFrame(c.value) in Repr &&
       RC.Valid(c.value) &&
       RBS.Containers(model)[i] == RC.Elements(c.value))
    }

    method In (x: nat32) returns (present: bool)
      ensures present == RBS.InRBitmapModel(x, model)

    method Insert(x: nat32)
      modifies Repr
      ensures model == RBS.InsertRBitmapModel(x, old(model))
  }
}