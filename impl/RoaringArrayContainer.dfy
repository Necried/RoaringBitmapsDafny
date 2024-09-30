include "../utils/Utils.dfy"
include "../utils/Permutations.dfy"
include "../functional/Specification.dfy"
include "Conversion.dfy"

module RoaringArrayBottom {
  import opened U = Utils
  import opened CS = ContainerSpecification
  import opened C = Conversion
  import opened P = Permutations

  class RoaringArrayBottom {
    var cardinality: nat
    var elems: array<nat16>
    ghost var Elements: CS.Container
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      Repr == {this, elems} &&
      // RoaringArray's cardinality is equal to length of its elems
      elems.Length == 4096 &&
      // RoaringArray's cardinality cannot exceed 4096
      cardinality <= elems.Length &&
      // RoaringArray elements are sorted
      (forall i,j :: 0 <= i < j < cardinality ==> elems[i] < elems[j]) &&
      // RoaringArrayElements convert `elems` into a set
      Elements == RoaringArrayElements(elems[..cardinality])
    }

    constructor(x: nat16)
      ensures Valid() && fresh(Repr)
      ensures cardinality == 0 && Elements == EmptyContainer()
    {
      elems := new nat16[4096];
      cardinality := 0;
      Elements := EmptyContainer();
      new;
      Repr := {this, elems};
      elems[0] := x;
    }

    constructor InitFromArray(arr: array<nat16>, c: nat)
      requires c <= arr.Length == 4096
      requires forall i :: 0 <= i < c ==> arr[i] < U.Exp(2, 16)
      requires forall i,j :: 0 <= i < j < c ==>
                               arr[i] < arr[j]
      ensures Valid()
    {
      elems := arr;
      cardinality := c;
      new;
      Repr := {this, elems};
      Elements := RoaringArrayElements(elems[..cardinality]);
    }

    method In(x: nat16) returns (present: bool)
      requires Valid()
      ensures present == (InContainer(x, Elements))
    {
      var isPresent, foundIndex := Contains(elems, cardinality, x);
      present := isPresent;
    }

    method {:vcs_split_on_every_assert} Insert(x: nat16)
      requires Valid() && cardinality < 4096
      modifies Repr
      ensures Valid() && Repr == old(Repr)
      ensures Elements == InsertContainer(x, old(Elements))
    {
      var present, insertIndex := Contains(elems, cardinality, x);
      if !present {
        assert !InContainer(x, Elements);
        assert x !in elems[..cardinality];
        InsertAtArrayIndex(elems, cardinality, x, insertIndex);
        cardinality := cardinality + 1;
        Elements := InsertContainer(x, Elements);
        InsertCorrect(x, old(Elements));
        // assert old(elems[..cardinality]) == old(elems[0..insertIndex]) + old(elems[insertIndex..cardinality]);
        // RoaringArrayElements convert `elems` into a set
        // Requires the SingletonInsert lemma below
        assert elems[..cardinality] == old(elems[0..insertIndex]) + [x] + old(elems[insertIndex..cardinality]);
        // assert P.NoDuplicateSeq(elems[..cardinality]);
        assert Elements.elems == old(Elements).elems + {x};
        assert Elements == RoaringArrayElements(elems[..cardinality]);
        assert Valid();
      } else {
        assert InContainer(x, Elements);
      }
    }

/*
    lemma SingletonInsert(s: seq<nat16>, index: nat, elem: nat16)
      requires index <= |s|
      requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
      ensures RoaringArrayElements(s[..index] + [elem] + s[index..]) == 
              RoaringArrayElements(s[..index] + s[index..]) + {elem}
    {
      calc {
        RoaringArrayElements(s[..index] + [elem] + s[index..]);
      =={ SetSplit(s[..index], [elem] + s[index..]);
          U.SeqAssociative(s[..index], [elem], s[index..]); }
        RoaringArrayElements(s[..index]) + RoaringArrayElements([elem] + s[index..]);
      =={ FrontElemSplit(elem, s[index..]); }
        RoaringArrayElements(s[..index]) + RoaringArrayElements(s[index..]) + ({elem});
      =={ SetSplit(s[..index], s[index..]); }
        RoaringArrayElements(s[..index] + s[index..]) + {elem};
      }
    }

    lemma SetSplit(s1: seq<nat16>, s2: seq<nat16>)
      // requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
      ensures RoaringArrayElements(s1 + s2) == RoaringArrayElements(s1) + RoaringArrayElements(s2)
    {
      if s1 == [] {
        calc {
          RoaringArrayElements([] + s2);
        ==
          set x: nat | 0 <= x < |[] + s2| :: ([] + s2)[x];
        =={ assert [] + s2 == s2; }
          set x: nat | 0 <= x < |s2| :: (s2)[x];
        ==
          RoaringArrayElements(s2);
        }
      } else {
        calc {
          RoaringArrayElements(s1 + s2);
        =={ assert s1 == [s1[0]] + s1[1..];
            U.SeqAssociative([s1[0]], s1[1..], s2); }
          RoaringArrayElements([s1[0]] + (s1[1..] + s2));
        =={ FrontElemSplit(s1[0], s1[1..] + s2); }
          ({s1[0]}) + RoaringArrayElements(s1[1..] + s2);
        =={ SetSplit(s1[1..], s2); }
          ({s1[0]}) + RoaringArrayElements(s1[1..]) + RoaringArrayElements(s2);
          // ==
          //  RoaringArrayElements(s1) + RoaringArrayElements(s2);
        }
      }
    }

    lemma SingletonElem(elem: nat16)
      ensures RoaringArrayElements([elem]) == {elem}
    {
      calc {
        RoaringArrayElements([elem]);
      ==
        set x: nat | 0 <= x < |[elem]| :: [elem][x];
      ==
        set x: nat | x == 0:: [elem][x];
      =={ assert [elem][0] == elem; }
        ({elem});
      }
    }

    lemma FrontElemSplit(elem: nat16, s: seq<nat16>)
      ensures RoaringArrayElements([elem] + s) == {elem} + RoaringArrayElements(s)
    {
      calc {
        RoaringArrayElements([elem] + s);
      ==
        set x: nat | 0 <= x < |[elem] + s| :: ([elem] + s)[x];
      ==
        (set x: nat | x == 0 :: ([elem] + s)[x]) +
        (set x: nat | (1 <= x < |[elem] + s|) :: ([elem] + s)[x]);
      =={ assert ([elem] + s)[0] == elem;
          SingletonElem(elem); }
        ({elem}) + (set x: nat | (1 <= x < |[elem] + s|) :: ([elem] + s)[x]);
      =={ RedundantBottomRange(elem, s); }
        ({elem}) + (set x: nat | (0 <= x < |s|) :: s[x]);
      ==
        ({elem}) + RoaringArrayElements(s);
      }
    }

    lemma RedundantBottomRange(elem: nat16, s: seq<nat16>)
      ensures (set x: nat | (1 <= x < |[elem] + s|) :: ([elem] + s)[x]) == (set x: nat | (0 <= x < |s|) :: s[x])
    {
      var s' := [elem] + s;
      assert (set x: nat | 1 <= x < |s'| :: s'[x]) == (set x: nat | 0 <= x < |s'[1..]| :: s'[1..][x]);
    } */
  }

}

