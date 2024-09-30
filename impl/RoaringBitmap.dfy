include "../utils/Utils.dfy"
include "../functional/Specification.dfy"
include "Conversion.dfy"
include "RoaringArrayContainer.dfy"
include "RoaringBitmapContainer.dfy"
include "../utils/Bitvector.dfy"

module RoaringBitmap {
  import opened U = Utils
  import C = Conversion
  import RBS = RoaringBitmapSpecification
  import CS = ContainerSpecification
  import BV = BitVec64
  import opened RBB = RoaringBitmapBottom
  import opened RAB = RoaringArrayBottom
  import RBU = RoaringBitsetUtils

  /*
  ghost function ConstructModel(topChunks: array<nat16>, containers: array<GhostOption<RoaringContainer>>, size: nat16): RBS.RBitmapModel
    reads topChunks, containers
    requires topChunks.Length == containers.Length == Exp(2, 16)
    requires (forall i, j :: 0 <= i < j < size ==> topChunks[i] < topChunks[j])
    requires forall i :: 0 <= i < size ==> 
      var cIndex := topChunks[i];
      containers[cIndex] != None && CS.Valid(containers[cIndex].value.Elements)
    ensures var model := ConstructModel(topChunks, containers, size);
      RBS.Valid(model)
  */

  class RBitmap {
    ghost var Repr: set<object>
    ghost var model: RBS.RBitmapModel

    var topChunks: array<nat16>
    var containers: array<GhostOption<RoaringContainer>>
    var size: nat16


    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr && topChunks in Repr && containers in Repr

      && topChunks.Length == containers.Length == U.Exp(2, 16)
      && size <= topChunks.Length && size <= containers.Length && size == |model|

      // The underlying model is valid
      && RBS.Valid(model)

      // Top-level indices corresponds to the model's topChunks
      && topChunks[..size] == RBS.TopChunks(model)

      && (forall i :: 0 <= i < size ==>
                     && ReprValid(i)
                     // Each container element corresponds to the set mapped to by topChunks[i]
                     && model[i].1 == containers[topChunks[i]].value.Elements)
      
      // && (forall i :: 0 <= i < Exp(2, 16) && i !in topChunks[..size] ==> containers[i] == None)


      && (forall i, j :: 0 <= i < j < size && containers[topChunks[i]].value in Repr && containers[topChunks[j]].value in Repr ==>
                        containers[topChunks[i]].value.Repr !! containers[topChunks[j]].value.Repr)

      && (forall i, j :: 0 <= i < j < size  ==> topChunks[i] < topChunks[j])
    }

    ghost predicate ReprValid(i: nat16) 
      reads this, Repr
      requires topChunks in Repr && containers in Repr
      requires i < size
      requires topChunks.Length == containers.Length == U.Exp(2, 16)
    {
      var x := topChunks[i];
      // Initialized elements are not None
      && containers[x] != None
      // Specification of what belongs in Repr
      && containers[x].value in Repr && containers[x].value.Repr <= Repr
      && this !in containers[x].value.Repr
      // Ensures that each array element's Repr does not have circular references to this classes' array objects
      && containers[x].value.Repr !! {topChunks, containers}
      // All container values must be valid
      && containers[x].value.Valid()

      // Ensures that all array object Repr's are disjoint
      // (forall i, j :: 0 <= i < j < size && containers[topChunks[i]].value in Repr && containers[topChunks[j]].value in Repr ==>
      //                  containers[topChunks[i]].value.Repr !! containers[topChunks[j]].value.Repr)
      
    }

    method In (x: nat32) returns (present: bool)
      requires Valid()
      ensures present == RBS.InRBitmapModel(x, model)
    {
      var (topChunk, botChunk) := ChunksFromElem(x);
      var isPresent, _ := U.Contains(topChunks, size, topChunk);
      if isPresent {
        present := containers[topChunk].value.In(botChunk);
      } else {
        present := false;
      }
    }

    method {:vcs_split_on_every_assert} {:timeLimit 40} Insert(elem: nat32)
      requires Valid()
      modifies Repr
      ensures fresh(Repr - old(Repr))
      ensures Valid() // && Repr == old(Repr)
      ensures model == RBS.InsertRBitmapModel(elem, old(model))
    {
      var (topChunk, botChunk) := ChunksFromElem(elem);
      var isPresent, seqIndex := U.Contains(topChunks, size, topChunk);
      if isPresent {
        assert topChunk in topChunks[..size];
        assert topChunk in RBS.TopChunks(model);
        assert containers[topChunk].value.Valid();
        assert forall i :: 0 <= i < size && i != seqIndex ==> ReprValid(i);
        containers[topChunk].value.Insert(botChunk);
        Repr := Repr + {containers[topChunk].value} + containers[topChunk].value.Repr;
        model := RBS.InsertRBitmapModel(elem, model);
        assert forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i];
          old(containers[x].value) == containers[x].value;
        assert forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i];
          && containers[x].value.Valid();
        assert ReprValid(seqIndex);
        assert Valid();
      } else {
        

        assume {:axiom} size < containers.Length && size < Exp(2, 16) - 1;
        var newRoaringArrayBottom := new RoaringContainer.InitSingletonRoaringArray(botChunk);
        // assert newRoaringArrayBottom.Repr == 
        //  {newRoaringArrayBottom, newRoaringArrayBottom.arrayContainer, newRoaringArrayBottom.arrayContainer.elems};
        InsertAtArrayIndex(topChunks, size, topChunk, seqIndex);
        assert old(topChunks[..size]) == old(topChunks[0..seqIndex]) + old(topChunks[seqIndex..size]);
        assert topChunks[..size+1] == 
          old(topChunks[0..seqIndex]) + [topChunk] + old(topChunks[seqIndex..size]);
        // assume {:axiom} containers[topChunk] == None;
        containers[topChunk] := Some(newRoaringArrayBottom);
        assert topChunks[seqIndex] == topChunk;
        Repr := Repr + {newRoaringArrayBottom} + newRoaringArrayBottom.Repr;
        size := size + 1;
        // assert model.Keys == (set i | 0 <= i < size :: topChunks[i]);
        model := RBS.InsertRBitmapModel(elem, model);

        assert topChunks[..size] == 
          old(topChunks[0..seqIndex]) + [topChunk] + old(topChunks[seqIndex..size]);
        assert old(topChunks[0..seqIndex]) == topChunks[0..seqIndex];
        assume {:axiom} forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i]; 
          containers[x] != None;
        assert forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i]; 
          old(containers[x].value) == containers[x].value;
        assert topChunks[seqIndex] == topChunk;
        assert containers[topChunk].value == newRoaringArrayBottom;
        assert model == RBS.InsertRBitmapModel(elem, old(model));
        /*
        // Specification of what belongs in Repr
        assert forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i];
        && containers[x].value in Repr && containers[x].value.Repr <= Repr;
        assert forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i];
        && this !in containers[x].value.Repr;
        // Ensures that each array element's Repr does not have circular references to this classes' array objects
        
        assert forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i];
        && containers[x].value.Repr !! {topChunks, containers};
        
        // All container values must be valid
        assert forall i :: 0 <= i < size && i != seqIndex ==> var x := topChunks[i];
        && containers[x].value.Valid();
        */

        model := RBS.InsertRBitmapModel(elem, model);
        assume {:axiom} Valid();

      }
    }

    /*
    method Append(topChunk: nat16, rc: RoaringContainer, c: nat)
      requires Valid() && size < Exp(2, 16) - 1
      requires rc.Valid()
      requires forall i :: 0 <= i < size ==> topChunk > topChunks[i]
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures size == old(size) + 1
      ensures topChunks[..size] == topChunks[..old(size)] + [topChunk]
      ensures containers[topChunk] == Some(rc)
      ensures model == old(model) + [(topChunk, rc.Elements)]
    {
      topChunks[size] := topChunk;
      containers[topChunk] := Some(rc);
      size := size + 1;
      model := model + [(topChunk, rc.Elements)];
      Repr := Repr + {rc} + rc.Repr;
    }
    */

    method {:vcs_split_on_every_assert} AppendBitmap(topChunk: nat16, bmap: array<bv64>)
      requires Valid() && size < Exp(2, 16) - 1
      requires bmap.Length == 1024
      requires RBU.Cardinality(bmap[..]) >= 4096
      requires forall i :: 0 <= i < size ==> topChunk > topChunks[i]
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures size == old(size) + 1
      ensures topChunks[..size] == topChunks[..old(size)] + [topChunk]
      ensures model == old(model) + [(topChunk, C.RoaringBitmapElements(bmap[..]))]
    {
      topChunks[size] := topChunk;
      var c := RBB.ComputeCardinality(bmap);
      var rbMap := RBB.MkRoaringBitmapBottom(bmap, c);
      var rbContainer := new RoaringContainer.InitRoaringBitmap(rbMap);
      containers[topChunk] := Some(rbContainer);
      size := size + 1;
      model := model + [(topChunk, rbContainer.Elements)];
      Repr := Repr + {rbContainer} + rbContainer.Repr;
      assert forall i :: 0 <= i < size - 1 ==> ReprValid(i);
      assert (forall i, j :: 0 <= i < j < size && containers[topChunks[i]].value in Repr 
                     && containers[topChunks[j]].value in Repr ==>
                     containers[topChunks[i]].value.Repr !! containers[topChunks[j]].value.Repr);
    }

  /*
    method AppendArray(topChunk: nat16, arr: array<nat16>)
      requires Valid() && size < Exp(2, 16) - 1
      requires arr.Length == 4096
      requires RAB.Cardinality(bmap[..]) >= 4096
      requires forall i :: 0 <= i < size ==> topChunk > topChunks[i]
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures size == old(size) + 1
      ensures topChunks[..size] == topChunks[..old(size)] + [topChunk]
      ensures model == old(model) + [(topChunk, C.RoaringBitmapElements(bmap[..]))]
  */
  }

  // ghost function UnionAt()

/*
  method Union(bmap1: RBitmap, bmap2: RBitmap) returns (bmapRes: RBitmap)
    requires bmap1.Valid() && bmap2.Valid()
    ensures bmapRes.Valid()
  {
    var p1, p2, n := 0, 0, 0;
    var collisions := 0;
    var newTopChunks := new nat16[U.Exp(2, 16)];
    var newContainers := new (GhostOption<RoaringContainer>)[U.Exp(2, 16)];
    ghost var numCollisions := |(set i | 0 <= i < bmap1.size :: bmap1.topChunks[i]) * (set i | 0 <= i < bmap2.size :: bmap2.topChunks[i])|;
    ghost var unionSize := bmap1.size + bmap2.size - numCollisions;
    assume {:axiom} unionSize <= U.Exp(2, 16);

    while p1 != bmap1.size || p2 != bmap2.size
      invariant newTopChunks.Length == newContainers.Length == U.Exp(2, 16)
      invariant 0 <= p1 <= bmap1.size <= bmap1.topChunks.Length &&
                0 <= p2 <= bmap2.size <= bmap2.topChunks.Length
      invariant 0 <= n < U.Exp(2, 16)
      /*
      invariant collisions == |(set i | 0 <= i < p1 :: bmap1.topChunks[i]) * (set i | 0 <= i < p2 :: bmap2.topChunks[i])|
      invariant 0 <= collisions <= numCollisions
      invariant 0 <= n <= unionSize
      invariant forall i :: 0 <= i < n ==>
        newTopChunks[i] in bmap1.topChunks[..p1] || newTopChunks[i] in bmap2.topChunks[..p2]
      invariant forall i :: 0 <= i < n ==>
        p1 == bmap1.size || newTopChunks[i] < bmap1.topChunks[p1]
      invariant forall i :: 0 <= i < n ==>
        p2 == bmap2.size || newTopChunks[i] < bmap2.topChunks[p2]
      invariant forall i :: i in newTopChunks[..n] ==>
        newContainers[i] != None
      // invariant forall i :: i in bmap1.topChunks[..p1] && i in bmap2.topChunks[..p2] ==>
      //   i in newTopChunks[..n] &&
      //  newContainers[i].value.Elements == bmap1.containers[i].value.Elements + bmap2.containers[i].value.Elements
      invariant bmap1.Valid() && bmap2.Valid()
      // invariant forall i, j :: 0 <= i < j < n ==>
      //   newTopChunks[i] < newTopChunks[j]
      */
      decreases U.Exp(2, 16) - n

    {
      if p1 == bmap1.size {
        var containerIdx := bmap2.topChunks[p2];
        newTopChunks[n] := containerIdx;
        newContainers[containerIdx] := bmap2.containers[containerIdx];
        p2 := p2 + 1;
      } else if p2 == bmap2.size {
        var containerIdx := bmap1.topChunks[p1];
        newTopChunks[n] := containerIdx;
        newContainers[containerIdx] := bmap1.containers[containerIdx];
        p1 := p1 + 1;
      } else {
        var x, y := bmap1.topChunks[p1], bmap2.topChunks[p2];
        assert bmap1.containers[x] != None && bmap2.containers[y] != None;
        if {
          case x < y => {
            newTopChunks[n] := x;
            newContainers[x] := bmap1.containers[x];
            p1 := p1 + 1;
          }
          case x > y => {
            newTopChunks[n] := y;
            newContainers[y] := bmap2.containers[y];
            p2 := p2 + 1;
          }
          case x == y => {
            newTopChunks[n] := x;
            var unionedContainers := UnionContainers(bmap1.containers[x].value, bmap2.containers[y].value);
            newContainers[x] := Some(unionedContainers);
            p1, p2 := p1 + 1, p2 + 1;
            collisions := collisions + 1;
          }
        }
      }
      n := n + 1;
    }

    ghost var model := RBS.UnionRBitmap(bmap1.model, bmap2.model);
    assume {:axiom} newTopChunks.Length == newContainers.Length == U.Exp(2, 16);
    assume {:axiom} n <= newTopChunks.Length && n <= newContainers.Length && n == |model|;
    assume {:axiom} forall i :: 0 <= i < n ==>  0 <= newTopChunks[i] < U.Exp(2, 16) &&
                                       forall j :: i < j < n ==> newTopChunks[i] < newTopChunks[j];
    assume {:axiom} forall i :: 0 <= i < n ==>
                         newContainers[i] != None && newContainers[i].value.Valid() &&
                         newTopChunks[i] in model && model[newTopChunks[i]] == newContainers[i].value.Elements;
    bmapRes := new RBitmap.InitFromExisting(newTopChunks, newContainers, n, model);
  }
*/
  datatype RoaringContainerObject
    = RoaringArray(arr: RoaringArrayBottom)
    | RoaringBitmap(bmap: RoaringBitmapBottom)

  class {:autocontracts} RoaringContainer {
    ghost var Elements: CS.Container
    ghost var Repr: set<object>
    var container: RoaringContainerObject

    ghost predicate Valid()
    {
      match container {
        case RoaringArray(arr) => 
          this in Repr && arr in Repr && arr.Repr <= Repr &&
          arr.Valid() &&
          Elements == arr.Elements
        case RoaringBitmap(bmap) =>
          this in Repr && bmap in Repr && bmap.Repr <= Repr &&
          bmap.Valid() &&
          Elements == bmap.Elements
      }
    }


    constructor InitSingletonRoaringArray(x: nat16)
      ensures container.RoaringArray?
      ensures fresh(container.arr)
      ensures Elements == CS.EmptyContainer()
      /*
    {
      arrayContainer := new RoaringArrayBottom(x);
      bmapContainer := null;
      containerType := RoaringArray;
      new;
      Elements := arrayContainer.Elements;
      Repr := {this, arrayContainer, arrayContainer.elems};
    } */

    constructor InitRoaringBitmap(bmap: RoaringBitmapBottom)
      requires bmap.Valid()
      ensures container.RoaringBitmap?
      ensures Elements == bmap.Elements
    /*{
      bmapContainer := bmap;
      arrayContainer := null;
      containerType := RoaringBitmap;
      new;
      Elements := bmapContainer.Elements;
      Repr := {this, bmapContainer, bmapContainer.bmaps};
    }*/

    constructor InitRoaringArray(arr: RoaringArrayBottom)
      requires arr.Valid()
      ensures container.RoaringArray?
      ensures Elements == arr.Elements
    /*{
      arrayContainer := arr;
      bmapContainer := null;
      containerType := RoaringArray;
      new;
      Elements := arrayContainer.Elements;
      Repr := {this, arrayContainer, arrayContainer.elems};
    }*/

    method In(x: nat16) returns (present: bool)
      ensures present == (CS.InContainer(x,Elements))
    {
      match container {
        case RoaringArray(arr) => present := arr.In(x);
        case RoaringBitmap(bmap) => present := bmap.In(x);
      }
    }

    method Insert(x: nat16)
      // modifies Repr
      ensures Repr == old(Repr)
      ensures Elements == CS.InsertContainer(x, old(Elements))
    {
      match container {
        case RoaringArray(_) =>
          if container.arr.cardinality == 4096 {
            var bmapArray := C.ConvertArrayToBitmap(container.arr.elems);
            var bmapContainer := 
              MkRoaringBitmapBottom(bmapArray, 4096); // new RoaringBitmapBottom.InitFromBitmaps(bmapArray);
            container := RoaringBitmap(bmapContainer);
            // Repr := {this, bmapContainer, bmapContainer.Repr};
            Insert(x);
          } else {
            container.arr.Insert(x);
            Elements := CS.InsertContainer(x, Elements);
          }
        case RoaringBitmap(_) =>
          container.bmap.Insert(x);
          Elements := CS.InsertContainer(x, Elements);
          // Repr := Repr + {bmapContainer, bmapContainer.bmaps};
      }


      /*
      match containerType
      case RoaringArray =>
        if arrayContainer.cardinality == 4096 {
          var bmapArray := C.ConvertArrayToBitmap(arrayContainer.elems);
          bmapContainer := 
            new RBB.RoaringBitmapBottom.InitFromBitmaps(bmapArray, arrayContainer.cardinality);
          arrayContainer := null;
          containerType := RoaringBitmap;
          Repr := Repr + {bmapContainer, bmapContainer.bmaps};
          Insert(x);
        } else {
          arrayContainer.Insert(x);
          Elements := arrayContainer.Elements;
          Repr := Repr + {arrayContainer, arrayContainer.elems};
        }
      case RoaringBitmap =>
        bmapContainer.Insert(x);
        Elements := bmapContainer.Elements;
        Repr := Repr + {bmapContainer, bmapContainer.bmaps};
        */
    }
  }

  method UnionRoaringBitmapBottoms(rb1: RoaringBitmapBottom, rb2: RoaringBitmapBottom)
    returns (rbRes: RoaringContainer)
    requires rb1.Valid() && rb2.Valid()
    ensures rbRes.Valid() && fresh(rbRes)
    ensures rbRes.Elements == CS.UnionContainers(rb1.Elements, rb2.Elements)
  {
    var tempBv64s := new bv64[1024];
    ghost var specArray := new bv64[1024];
    forall i | 0 <= i < specArray.Length
      ensures specArray[i] == rb1.bmaps[i] | rb2.bmaps[i]
    {
      assume {:axiom} specArray[i] == rb1.bmaps[i] | rb2.bmaps[i];
    }
    var c := 0;
    var i := 0;
    while i != tempBv64s.Length
      invariant forall i :: 0 <= i < specArray.Length
                            ==> specArray[i] == rb1.bmaps[i] | rb2.bmaps[i]
      invariant 0 <= i <= tempBv64s.Length && tempBv64s.Length == 1024
      invariant forall k :: 0 <= k < i ==>
                              tempBv64s[k] == specArray[k]
      invariant c == RBU.CardinalityTo(tempBv64s[..], i)
    {
      assert c == RBU.CardinalityTo(tempBv64s[..], i);
      tempBv64s[i] := rb1.bmaps[i] | rb2.bmaps[i];
      // AtLeastBitwiseOr(rb1.bmaps[i], rb2.bmaps[i]);
      c := c + BV.Popcnt(tempBv64s[i]);
      RBU.CardinalitySplitLast(tempBv64s[..], i);
      i := i + 1;
      assert c == RBU.CardinalityTo(tempBv64s[..], i);
      // assume {:axiom} RoaringBitmapElementsUpTo(tempBv64s, i) ==
      //       RoaringBitmapElementsUpTo(rb1.bmaps, i) + RoaringBitmapElementsUpTo(rb2.bmaps, i);
    }
    assume {:axiom} 4096 < c < Exp(2, 16);
    RBU.CardinalityTo1024(tempBv64s[..]);
    var rbBottom := new RoaringBitmapBottom.InitFromBitmaps(tempBv64s, c);
    rbRes := new RoaringContainer.InitRoaringBitmap(rbBottom);
    assume {:axiom} rbRes.Elements == CS.UnionContainers(rb1.Elements, rb2.Elements);
  }

  method UnionRoaringBitmapAndArray(rb: RoaringBitmapBottom, arr: RoaringArrayBottom) 
    returns (newContainer: RoaringContainer)
    requires rb.Valid() && arr.Valid()
    ensures fresh(newContainer)
    ensures newContainer.Valid()
    ensures unchanged(rb) && unchanged(arr)
    ensures newContainer.Elements == CS.UnionContainers(rb.Elements, arr.Elements)
  {
    var rbRes := new RoaringBitmapBottom.InitFromBitmaps(rb.bmaps, rb.cardinality);
    var n := 0;
    while n != arr.cardinality
      invariant fresh(rbRes.Repr)
      invariant 0 <= n <= arr.cardinality
      invariant rbRes.Valid()
      invariant forall i :: 0 <= i < arr.cardinality ==>
                              arr.elems[i] < U.Exp(2, 16)
      invariant forall i :: 0 <= i < n ==>
                              rbRes.In(arr.elems[i])
    {
      rbRes.Insert(arr.elems[n]);
      n := n + 1;
    }
    newContainer := new RoaringContainer.InitRoaringBitmap(rbRes);
    assume {:axiom} newContainer.Elements == CS.UnionContainers(rb.Elements, arr.Elements);
  }

  method UnionRoaringArraysSmallCardinality(arr1: RoaringArrayBottom, arr2: RoaringArrayBottom)
    returns (container: RoaringContainer)
    requires arr1.cardinality + arr2.cardinality < 4096
    requires arr1.Valid() && arr2.Valid()
    ensures container.Valid() && fresh(container)
    ensures container.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements)
  {
    var tempArr := new nat16[4096];
    var p1, p2, n := 0, 0, 0;
    while p1 != arr1.cardinality || p2 != arr2.cardinality
      invariant 0 <= n <= p1 + p2 < 4096
      invariant tempArr.Length == 4096
      invariant 0 <= p1 <= arr1.cardinality < arr1.elems.Length &&
                0 <= p2 <= arr2.cardinality < arr2.elems.Length
      invariant forall i :: 0 <= i < n ==>
                              tempArr[i] in arr1.elems[..p1] || tempArr[i] in arr2.elems[..p2]
      invariant arr1.Valid() && arr2.Valid()
      // The next two invariants are the linchpin of verifying the correctness of merging!
      invariant forall i :: 0 <= i < n ==>
                              p1 == arr1.cardinality || tempArr[i] < arr1.elems[p1]
      invariant forall i :: 0 <= i < n ==>
                              p2 == arr2.cardinality || tempArr[i] < arr2.elems[p2]
      invariant forall i, j :: 0 <= i < j < n ==>
                                 tempArr[i] < tempArr[j]
      decreases arr1.cardinality + arr2.cardinality - n
    {
      if p1 == arr1.cardinality {
        tempArr[n] := arr2.elems[p2];
        p2 := p2 + 1;
      } else if p2 == arr2.cardinality {
        tempArr[n] := arr1.elems[p1];
        p1 := p1 + 1;
      } else {
        var x, y := arr1.elems[p1], arr2.elems[p2];
        if {
          case x < y => {
            tempArr[n] := x;
            p1 := p1 + 1;
          }
          case x > y => {
            tempArr[n] := y;
            p2 := p2 + 1;
          }
          case x == y => {
            tempArr[n] := x;
            p1, p2 := p1 + 1, p2 + 1;
          }
        }
      }
      n := n + 1;
    }
    var arrRes := new RoaringArrayBottom.InitFromArray(tempArr, n);
    container := new RoaringContainer.InitRoaringArray(arrRes);
    assume {:axiom} container.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements);
  }

  /*
  While converting to a RoaringBitmapBottom would make verification easier, we cannot
  initialize cardinality > 4096 as the starting point is an empty bitmap.
  This violates the validity clause - therefore we operate on just the underlying
  container
  */
  method {:timeLimit 30} UnionRoaringArraysBigCardinality(arr1: RoaringArrayBottom, arr2: RoaringArrayBottom)
    returns (res: RoaringContainer)
    requires arr1.cardinality + arr2.cardinality >= 4096
    requires arr1.Valid() && arr2.Valid()
    ensures res.Valid() && fresh(res)
    ensures res.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements)
  {
    var tempBv64s, c := new bv64[1024], 0;
    var n := 0;
    while n != arr1.cardinality
      invariant 0 <= n <= arr1.cardinality
      invariant arr1.Valid()
      invariant tempBv64s.Length == 1024
      invariant forall i :: 0 <= i < n ==>
                              var bmapIndex, bvIndex := arr1.elems[i] / U.Exp(2, 6), arr1.elems[i] % U.Exp(2, 6);
                              arr1.elems[i] < U.Exp(2, 16) && tempBv64s[bmapIndex] & (1 << bvIndex) != 0
      invariant fresh(tempBv64s)
    {
      var bmapIndex, bvIndex := arr1.elems[n] / U.Exp(2, 6), arr1.elems[n] % U.Exp(2, 6);
      tempBv64s[bmapIndex] := tempBv64s[bmapIndex] | (1 << bvIndex);
      n := n + 1;
    }

    var m := 0;
    while m != arr2.cardinality
      invariant 0 <= m <= arr2.cardinality
      invariant arr2.Valid()
      invariant tempBv64s.Length == 1024
      invariant forall i :: 0 <= i < m ==>
                              var bmapIndex, bvIndex := arr2.elems[i] / U.Exp(2, 6), arr2.elems[i] % U.Exp(2, 6);
                              arr2.elems[i] < U.Exp(2, 16) && tempBv64s[bmapIndex] & (1 << bvIndex) != 0
      invariant fresh(tempBv64s)
    {
      var bmapIndex, bvIndex := arr2.elems[m] / U.Exp(2, 6), arr2.elems[m] % U.Exp(2, 6);
      tempBv64s[bmapIndex] := tempBv64s[bmapIndex] | (1 << bvIndex);
      m := m + 1;
    }
    c := ComputeCardinality(tempBv64s);
    if c < 4096 {
      var roaringArray := C.ConvertBitmapToArray(tempBv64s);
      var roaringArrayBottom := new RAB.RoaringArrayBottom.InitFromArray(roaringArray, c);
      res := new RoaringContainer.InitRoaringArray(roaringArrayBottom);
    } else {
      var roaringBitmap := new RoaringBitmapBottom.InitFromBitmaps(tempBv64s, c);
      res := new RoaringContainer.InitRoaringBitmap(roaringBitmap);
    }
    assume {:axiom} res.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements);
  }


  /*
  method UnionContainers(c1: RoaringContainer, c2: RoaringContainer) returns (c: RoaringContainer)
    requires c1.Valid() && c2.Valid()
    ensures c.Valid() && fresh(c)
    ensures c.Elements == CS.UnionContainers(c1.Elements, c2.Elements)
  {
    match (c1.containerType, c2.containerType)
    case (RoaringBitmap, RoaringBitmap) =>
      c := UnionRoaringBitmapBottoms(c1.bmapContainer, c2.bmapContainer);
    case (RoaringArray, RoaringArray) =>
      if c1.arrayContainer.cardinality + c2.arrayContainer.cardinality < 4096 {
        c := UnionRoaringArraysSmallCardinality(c1.arrayContainer, c2.arrayContainer);
      } else {
        c := UnionRoaringArraysBigCardinality(c1.arrayContainer, c2.arrayContainer);
      }
    case (RoaringArray, RoaringBitmap) =>
      c := UnionRoaringBitmapAndArray(c2.bmapContainer, c1.arrayContainer);
    case (RoaringBitmap, RoaringArray) =>
      c := UnionRoaringBitmapAndArray(c1.bmapContainer, c2.arrayContainer);
  }

  method UnionRoaringBitmapBottoms(rb1: RoaringBitmapBottom, rb2: RoaringBitmapBottom)
    returns (rbRes: RoaringContainer)
    requires rb1.Valid() && rb2.Valid()
    ensures rbRes.Valid() && fresh(rbRes)
    ensures rbRes.Elements == CS.UnionContainers(rb1.Elements, rb2.Elements)
  {
    var tempBv64s := new bv64[1024];
    ghost var specArray := new bv64[1024];
    forall i | 0 <= i < specArray.Length
      ensures specArray[i] == rb1.bmaps[i] | rb2.bmaps[i]
    {
      assume {:axiom} specArray[i] == rb1.bmaps[i] | rb2.bmaps[i];
    }
    var c := 0;
    var i := 0;
    // assume {:axiom} RoaringBitmapElementsUpTo(tempBv64s, 0) ==
    //       RoaringBitmapElementsUpTo(rb1.bmaps, 0) + RoaringBitmapElementsUpTo(rb2.bmaps, 0);
    while i != tempBv64s.Length
      invariant forall i :: 0 <= i < specArray.Length
                            ==> specArray[i] == rb1.bmaps[i] | rb2.bmaps[i]
      invariant 0 <= i <= tempBv64s.Length && tempBv64s.Length == 1024
      invariant forall k :: 0 <= k < i ==>
                              tempBv64s[k] == specArray[k]
      // invariant c == RoaringBitmapSetBitsUpTo(specArray, i)
      // invariant RoaringBitmapElementsUpTo(tempBv64s, i) ==
      //          RoaringBitmapElementsUpTo(rb1.bmaps, i) + RoaringBitmapElementsUpTo(rb2.bmaps, i)
    {
      tempBv64s[i] := rb1.bmaps[i] | rb2.bmaps[i];
      // AtLeastBitwiseOr(rb1.bmaps[i], rb2.bmaps[i]);
      c := c + BV.Popcnt(tempBv64s[i]);
      i := i + 1;
      // assume {:axiom} RoaringBitmapElementsUpTo(tempBv64s, i) ==
      //       RoaringBitmapElementsUpTo(rb1.bmaps, i) + RoaringBitmapElementsUpTo(rb2.bmaps, i);
    }
    // EqualBmapsSetBits(specArray, tempBv64s, i);
    // assert forall k :: 0 <= k < 1024 ==>
    //  BV.Popcnt(rb1.bmaps[k] | rb2.bmaps[k]) >= BV.Popcnt(rb1.bmaps[k]);
    // PopcntMonotonicity(rb1.bmaps, rb2.bmaps);
    // assert RoaringBitmapSetBits(rb1.bmaps, i) <= RoaringBitmapSetBits(tempBv64s, i);
    assume {:axiom} c > 4096;
    // RoaringBitmapElementsUpTo1024(tempBv64s);
    // assume {:axiom} RoaringBitmapElements(tempBv64s) == RoaringBitmapElements(rb1.bmaps) + RoaringBitmapElements(rb2.bmaps);
    // UnionRoaringBitmapElements(rb1, rb2);
    var rbBottom := new RoaringBitmapBottom.InitFromBitmaps(tempBv64s, c);
    rbRes := new RoaringContainer.InitRoaringBitmap(rbBottom);
    assume {:axiom} rbRes.Elements == CS.UnionContainers(rb1.Elements, rb2.Elements);
  }

  method UnionRoaringBitmapAndArray(rb: RoaringBitmapBottom, arr: RoaringArrayBottom) returns (newContainer: RoaringContainer)
    requires rb.Valid() && arr.Valid()
    ensures fresh(newContainer)
    ensures newContainer.Valid()
    ensures unchanged(rb) && unchanged(arr)
    ensures newContainer.Elements == CS.UnionContainers(rb.Elements, arr.Elements)
  {
    var rbRes := new RoaringBitmapBottom.InitFromBitmaps(rb.bmaps, rb.cardinality);
    var n := 0;
    while n != arr.cardinality
      invariant fresh(rbRes.Repr)
      invariant 0 <= n <= arr.cardinality
      invariant rbRes.Valid()
      invariant forall i :: 0 <= i < arr.cardinality ==>
                              arr.elems[i] < U.Exp(2, 16)
      invariant forall i :: 0 <= i < n ==>
                              rbRes.In(arr.elems[i])
    {
      rbRes.Insert(arr.elems[n]);
      n := n + 1;
    }
    newContainer := new RoaringContainer.InitRoaringBitmap(rbRes);
    assume {:axiom} newContainer.Elements == CS.UnionContainers(rb.Elements, arr.Elements);
  }

  method UnionRoaringArraysSmallCardinality(arr1: RoaringArrayBottom, arr2: RoaringArrayBottom)
    returns (container: RoaringContainer)
    requires arr1.cardinality + arr2.cardinality < 4096
    requires arr1.Valid() && arr2.Valid()
    ensures container.Valid() && fresh(container)
    ensures container.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements)
  {
    var tempArr := new nat16[4096];
    var p1, p2, n := 0, 0, 0;
    while p1 != arr1.cardinality || p2 != arr2.cardinality
      invariant 0 <= n <= p1 + p2 < 4096
      invariant tempArr.Length == 4096
      invariant 0 <= p1 <= arr1.cardinality < arr1.elems.Length &&
                0 <= p2 <= arr2.cardinality < arr2.elems.Length
      invariant forall i :: 0 <= i < n ==>
                              tempArr[i] in arr1.elems[..p1] || tempArr[i] in arr2.elems[..p2]
      invariant arr1.Valid() && arr2.Valid()
      // The next two invariants are the linchpin of verifying the correctness of merging!
      invariant forall i :: 0 <= i < n ==>
                              p1 == arr1.cardinality || tempArr[i] < arr1.elems[p1]
      invariant forall i :: 0 <= i < n ==>
                              p2 == arr2.cardinality || tempArr[i] < arr2.elems[p2]
      invariant forall i, j :: 0 <= i < j < n ==>
                                 tempArr[i] < tempArr[j]
      decreases arr1.cardinality + arr2.cardinality - n
    {
      if p1 == arr1.cardinality {
        tempArr[n] := arr2.elems[p2];
        p2 := p2 + 1;
      } else if p2 == arr2.cardinality {
        tempArr[n] := arr1.elems[p1];
        p1 := p1 + 1;
      } else {
        var x, y := arr1.elems[p1], arr2.elems[p2];
        if {
          case x < y => {
            tempArr[n] := x;
            p1 := p1 + 1;
          }
          case x > y => {
            tempArr[n] := y;
            p2 := p2 + 1;
          }
          case x == y => {
            tempArr[n] := x;
            p1, p2 := p1 + 1, p2 + 1;
          }
        }
      }
      n := n + 1;
    }
    var arrRes := new RoaringArrayBottom.InitFromArray(tempArr, n);
    container := new RoaringContainer.InitRoaringArray(arrRes);
    assume {:axiom} container.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements);
  }

  /*
  While converting to a RoaringBitmapBottom would make verification easier, we cannot
  initialize cardinality > 4096 as the starting point is an empty bitmap.
  This violates the validity clause - therefore we operate on just the underlying
  container
  */
  method UnionRoaringArraysBigCardinality(arr1: RoaringArrayBottom, arr2: RoaringArrayBottom)
    returns (res: RoaringContainer)
    requires arr1.cardinality + arr2.cardinality >= 4096
    requires arr1.Valid() && arr2.Valid()
    ensures res.Valid() && fresh(res)
    ensures res.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements)
  {
    var tempBv64s, c := new bv64[1024], 0;
    var n := 0;
    while n != arr1.cardinality
      invariant 0 <= n <= arr1.cardinality
      invariant arr1.Valid()
      invariant tempBv64s.Length == 1024
      invariant forall i :: 0 <= i < n ==>
                              var bmapIndex, bvIndex := arr1.elems[i] / U.Exp(2, 6), arr1.elems[i] % U.Exp(2, 6);
                              arr1.elems[i] < U.Exp(2, 16) && tempBv64s[bmapIndex] & (1 << bvIndex) != 0
      invariant fresh(tempBv64s)
    {
      var bmapIndex, bvIndex := arr1.elems[n] / U.Exp(2, 6), arr1.elems[n] % U.Exp(2, 6);
      tempBv64s[bmapIndex] := tempBv64s[bmapIndex] | (1 << bvIndex);
      n := n + 1;
    }

    var m := 0;
    while m != arr2.cardinality
      invariant 0 <= m <= arr2.cardinality
      invariant arr2.Valid()
      invariant tempBv64s.Length == 1024
      invariant forall i :: 0 <= i < m ==>
                              var bmapIndex, bvIndex := arr2.elems[i] / U.Exp(2, 6), arr2.elems[i] % U.Exp(2, 6);
                              arr2.elems[i] < U.Exp(2, 16) && tempBv64s[bmapIndex] & (1 << bvIndex) != 0
      invariant fresh(tempBv64s)
    {
      var bmapIndex, bvIndex := arr2.elems[m] / U.Exp(2, 6), arr2.elems[m] % U.Exp(2, 6);
      tempBv64s[bmapIndex] := tempBv64s[bmapIndex] | (1 << bvIndex);
      m := m + 1;
    }

    if c <= 4096 {
      var roaringArray := C.ConvertBitmapToArray(tempBv64s);
      var roaringArrayBottom := new RAB.RoaringArrayBottom.InitFromArray(roaringArray, c);
      res := new RoaringContainer.InitRoaringArray(roaringArrayBottom);
    } else {
      var roaringBitmap := new RoaringBitmapBottom.InitFromBitmaps(tempBv64s, c);
      res := new RoaringContainer.InitRoaringBitmap(roaringBitmap);
    }
    assume {:axiom} res.Elements == CS.UnionContainers(arr1.Elements, arr2.Elements);
  }
  */

  /*
  method InsertAtArrayIndex(arr: array<nat>, elem: nat, index: nat) returns (res: array<nat>)
    requires 0 <= index <= arr.Length
    requires forall i,j :: 0 <= i < j < arr.Length ==> arr[i] < arr[j]
    requires forall i :: 0 <= i < index ==> arr[i] < elem
    requires forall i :: index <= i < arr.Length ==> elem < arr[i]
    requires forall i :: 0 <= i < arr.Length ==> arr[i] != elem
    ensures res.Length == arr.Length + 1
    ensures res[..] == arr[0..index] + [elem] + arr[index..arr.Length]
    ensures res[index] == elem
    ensures forall i,j :: 0 <= i < j < res.Length ==> res[i] < res[j] && res[i] != res[j]
    ensures fresh(res)
  {
    ghost var resSeq := arr[0..index] + [elem] + arr[index..arr.Length];
    res := new (nat)[arr.Length + 1];
    var n := 0;
    while n != res.Length
      invariant 0 <= n <= res.Length
      invariant |resSeq| == res.Length
      invariant forall i :: 0 <= i < n ==> res[i] == resSeq[i]
    {
      if n == index {
        res[n] := elem;
      } else if n > index {
        res[n] := arr[n - 1];
      } else {
        res[n] := arr[n];
      }
      n := n + 1;
    }
  }
  */

/*
  ghost function RoaringArrayElements(s: seq<nat16>): set<nat16>
  {
    set x: nat | 0 <= x < |s| :: s[x]
  }

  ghost function RoaringBitmapElements(bmapParam: array<bv64>): set<nat16>
    requires bmapParam.Length == 1024
    ensures var outputSet := RoaringBitmapElements(bmapParam);
            forall bmapIndex, mask :: 0 <= bmapIndex < 1024 && 0 <= mask < 64
                                      ==> (bmapParam[bmapIndex] & (1 << mask) != 0) == ((bmapIndex * U.Exp(2, 6) + mask) in outputSet)

  ghost function RoaringBitmapElementsUpTo(bmapParam: array<bv64>, i: nat): set<nat16>
    requires bmapParam.Length == 1024
    requires i <= bmapParam.Length
    ensures var outputSet := RoaringBitmapElementsUpTo(bmapParam, i);
            forall bmapIndex, mask :: 0 <= bmapIndex < i && 0 <= mask < 64
                                      ==> (bmapParam[bmapIndex] & (1 << mask) != 0) == ((bmapIndex * U.Exp(2, 6) + mask) in outputSet)
  /*
  {
    if i == 0 then {}
    else 
      (set n: nat | 0 <= n < 64 && (bmapParam[i] & (1 << n) != 0) :: i * U.Exp(2, 6) + n) 
      + RoaringBitmapElementsUpTo(bmapParam, i - 1)
  }
  */

  lemma RoaringBitmapElementsUpTo1024(bmapParam: array<bv64>)
    requires bmapParam.Length == 1024
    ensures RoaringBitmapElementsUpTo(bmapParam, 1024) == RoaringBitmapElements(bmapParam)

  lemma UnionRoaringBitmapElements(bmap1: RoaringBitmapBottom, bmap2: RoaringBitmapBottom)
    requires bmap1.Valid() && bmap2.Valid()
    ensures CS.Elements(CS.UnionContainers(bmap1.Elements, bmap2.Elements)) == 
            RoaringBitmapElements(bmap1.bmaps) + RoaringBitmapElements(bmap2.bmaps)

  ghost function RoaringBitmapSetBits(bmaps: array<bv64>): nat
    requires bmaps.Length == 1024
    reads bmaps
  {
    RoaringBitmapSetBitsUpTo(bmaps, 1024)
  }

  ghost function RoaringBitmapSetBitsUpTo(bmaps: array<bv64>, n: nat): nat
    requires bmaps.Length == 1024
    requires 0 <= n <= bmaps.Length
    decreases n
    reads bmaps
  {
    if n == 0 then 0 else RoaringBitmapSetBitsUpTo(bmaps, n-1) + BV.Popcnt(bmaps[n-1])
  }

  lemma EqualBmapsSetBits(bmap1: array<bv64>, bmap2: array<bv64>, n: nat)
    requires bmap1.Length == bmap2.Length == 1024
    requires n <= bmap1.Length
    requires forall i :: 0 <= i < n ==> bmap1[i] == bmap2[i]
    ensures RoaringBitmapSetBitsUpTo(bmap1, n) == RoaringBitmapSetBitsUpTo(bmap2, n)
  {

  }

  lemma AtLeastBitwiseOr(b1: bv64, b2: bv64)
    ensures BV.Popcnt(b1 | b2) >= BV.Popcnt(b1)

  lemma PopcntMonotonicity(rb1: array<bv64>, rb2: array<bv64>)
    requires rb1.Length == rb2.Length == 1024
    requires forall i :: 0 <= i < rb1.Length ==>
                           BV.Popcnt(rb1[i] | rb2[i]) >= BV.Popcnt(rb1[i])
    ensures RoaringBitmapSetBits(rb1) <= RoaringBitmapSetBits(rb2)

  // Hacker's Delight 2nd ed. See also Algorithm 2 in Chambi's paper
  method ConvertBitmapToArray(bmap: array<bv64>) returns (newContainer: RoaringArrayBottom)
    requires bmap.Length == 1024
    ensures newContainer.Valid() && fresh(newContainer)
  {
    var seqElems := [];
    var bmapIndex := 0;
    while bmapIndex != 1024
      invariant 0 <= bmapIndex <= 1024
    {
      var w := bmap[bmapIndex];
      while w != 0
        invariant w >= 0
        decreases w
      {
        var t := w & (-w);
        seqElems :=  seqElems + [BV.Popcnt(t - 1) * (bmapIndex + 1)];
        assume {:axiom} w > w & (w - 1);
        w := w & (w - 1);
      }
      bmapIndex := bmapIndex + 1;
    }
    assume {:axiom} |seqElems| <= 4096;
    assume {:axiom} forall i, j :: 0 <= i < j < |seqElems| ==> seqElems[i] < seqElems[j];
    var arrElems := new nat16[4096];
    forall i | 0 <= i < |seqElems| {
      arrElems[i] := seqElems[i];
    }
    newContainer := new RoaringArrayBottom.InitFromArray(arrElems, |seqElems|);
  }

  method ConvertArrayToBitmap(arr: array<nat16>) returns (newContainer: RoaringBitmapBottom)
    requires arr.Length == 4096
    ensures newContainer.Valid() && fresh(newContainer)
    ensures RoaringArrayElements(arr[..]) == newContainer.Elements
    ensures newContainer.cardinality == 4096
  {
    var tempBv64s, c := new bv64[1024], 0;
    var n := 0;
    while n != arr.Length
      invariant 0 <= n <= arr.Length
      invariant tempBv64s.Length == 1024
      invariant forall i :: 0 <= i < n ==>
                              var bmapIndex, bvIndex := arr[i] / U.Exp(2, 6), arr[i] % U.Exp(2, 6);
                              arr[i] < U.Exp(2, 16) && tempBv64s[bmapIndex] & (1 << bvIndex) != 0
      invariant fresh(tempBv64s)
    {
      var bmapIndex, bvIndex := arr[n] / U.Exp(2, 6), arr[n] % U.Exp(2, 6);
      tempBv64s[bmapIndex] := tempBv64s[bmapIndex] | (1 << bvIndex);
      n := n + 1;
    }

    assume {:axiom} n == RoaringBitmapSetBits(tempBv64s);
    newContainer := new RoaringBitmapBottom.InitFromBitmaps(tempBv64s, n);
    assume {:axiom} RoaringArrayElements(arr[..]) == newContainer.Elements;
  }

  method BinarySearch(a: array<nat16>, size: nat, key: nat) returns (n: int)
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

  method Contains(a: array<nat16>, size: nat, key: nat16) returns (present: bool, n: nat)
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
  */
}

/*
module TestHarness {
  import RB = RoaringBitmap
  import Spec = RoaringBitmapSpecification
  import U = Utils

  method CreateRB1() returns (rb1: RB.RBitmap)
    ensures rb1.Valid() && fresh(rb1)
  {
    rb1 := new RB.RBitmap();

    for i := 0 to 1000
      invariant fresh(rb1.Repr)
      invariant rb1.Valid()
    {
      rb1.Insert(i * 62);
    }
    for i := 0 to 100
      invariant fresh(rb1.Repr)
      invariant rb1.Valid()
    {
      rb1.Insert(4 * U.Exp(2, 16) + i);
    }
    for i := 0 to U.Exp(2, 15)
      invariant fresh(rb1.Repr)
      invariant rb1.Valid()
    {
      rb1.Insert(100 * U.Exp(2, 16) + i * 2);
    }
  }

  method CreateRB2() returns (rb2: RB.RBitmap)
    ensures rb2.Valid() && fresh(rb2)
  {
    rb2 := new RB.RBitmap();

    for i := 0 to 1000
      invariant fresh(rb2.Repr)
      invariant rb2.Valid()
    {
      rb2.Insert(i * 31);
    }

    for i := 0 to 100
      invariant fresh(rb2.Repr)
      invariant rb2.Valid()
    {
      rb2.Insert(5 * U.Exp(2, 16) + i);
    }
    for i := 0 to U.Exp(2, 15)
      invariant fresh(rb2.Repr)
      invariant rb2.Valid()
    {
      rb2.Insert(100 * U.Exp(2, 16) + (i + 1) * 2);
    }
  }

  method Main() {
    var rb1 := CreateRB1();
    var rb2 := CreateRB2();
    var rbUnion := RB.Union(rb1, rb2);
  }

  method TestRoaringContainer() {
    var rc := new RB.RoaringContainer.InitSingletonRoaringArray(100);
    assert rc.Valid();
    rc.Insert(12);
    assert rc.Valid();

    var ra: RB.RoaringArrayBottom :=  new RB.RoaringArrayBottom(100);
    // assert ra.cardinality == 0;
    // ra.Insert(12);
    var n := 0;
    while n != 10
      invariant 0 <= n <= 10
      invariant ra.Valid()
      invariant fresh(ra.Repr) // No need for a modifies clause on a freshly allocated object!
    {
      assume {:axiom} ra.cardinality < 4096;
      ra.Insert(n);
      n := n + 1;
    }
  }

  /*
    method TestRB() {
      var rbMap := new RB.RBitmap();
      rbMap.Insert(12);
      var inBMap := rbMap.In(12);
      var notInBMap := rbMap.In(13);
      assert inBMap;
      assert !notInBMap;
    }
  
  
    method TestU() {
      var bvTest: bv64 := 10;
      calc {
          U.Bv64ToSet(bvTest);
        == // variable substitution
          U.Bv64ToSet(10);
        == // Apply definition
          U.Bv64ToSetHelper(10, 0);
        == // Apply def
          U.Bv64ToSetHelper(5, 1);
        == // First element
          ((if (5 as bv64 & 1 == 0) then {} else {1}) + U.Bv64ToSetHelper(2, 2));
        == // Recurse
          ({1} + U.Bv64ToSetHelper(1, 3));
      }
      assert U.Bv64ToSet(bvTest) == {1, 3};
    }
  */
}
*/