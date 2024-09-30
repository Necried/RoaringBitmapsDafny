include "../utils/Utils.dfy"
include "../utils/SeqHelpers.dfy"
include "../utils/Permutations.dfy"
include "../utils/CollectionHelpers.dfy"

module ContainerSpecification {
  import opened U = Utils
  import opened C = CollectionHelpers

  datatype Container = 
      ArrayModel(elems: set<nat16>)
    | BitmapModel(elems: set<nat16>)
    | RunsModel(elems: set<nat16>)

  predicate Valid(container: Container) {
    match container
    case ArrayModel(s) => |s| <= 4096
    case BitmapModel(s) => |s| > 4096
    case RunsModel(s) =>
      var numRuns := CountRunsSet(s);
      if |s| > 4096 then numRuns <= 2047
      else numRuns < |s| / 2
  }

  function Elements(container: Container): set<nat16> {
    container.elems
  }

  predicate InContainer(x: nat16, container: Container) 
    requires Valid(container)
  {
    x in container.elems
  }

  function EmptyContainer(): Container {
    ArrayModel({})
  }

  function SingletonContainer(x: nat16): Container
    ensures Valid(SingletonContainer(x))
  {
    ArrayModel({x})
  }

  // The insertion function has a precondition that a container cannot 
  // contain a runs container; the container is supposed
  // to be immutable after all calls to insertions
  function InsertContainer(x: nat16, container: Container): Container
    requires Valid(container)
    requires !container.RunsModel?
    ensures Valid(container)
    ensures var newContainer := InsertContainer(x, container);
            Valid(newContainer) && InContainer(x, newContainer)
  {
    match container
    case ArrayModel(s) =>
      var s' := s + {x};
      if |s'| > 4096 then BitmapModel(s') else ArrayModel(s')
    case BitmapModel(s) =>
      var newContainer := BitmapModel(s + {x});
      UnionSingletonPreservesSetCardinality(s, x);
      newContainer
  }

  function UnionContainers(c1: Container, c2: Container): Container
    requires Valid(c1) && Valid(c2)
    ensures var newContainer := UnionContainers(c1, c2);
            Valid(newContainer) &&
            newContainer.elems == c1.elems + c2.elems
  {
    var s' := c1.elems + c2.elems;
    if |s'| > 4096
      then BitmapModel(s')
      else ArrayModel(s')
  }

  lemma UnionSingletonPreservesSetCardinality<T>(s: set<T>, x: T)
    ensures |s + {x}| >= |s|
  {
    if
      case x in s =>
        calc {
            s + {x};
          =={ assert x in s; }
            s;
        }
      case x !in s =>
  }

  lemma InsertCorrect(x: nat16, container: Container)
    requires Valid(container)
    requires !container.RunsModel?
    ensures Elements(InsertContainer(x, container)) == Elements(container) + {x}
  {

  }
}

module RoaringBitmapSpecification {
  import opened U = Utils
  import opened SeqHelpers = SeqHelpers
  import C = ContainerSpecification
  import P = Permutations

  type RBitmapModel = seq<(nat16, C.Container)>

  // type finarray<T, n> = arr: array<T> | arr.Length == n

  // The validity of the model closely follows the Roaring bitmap specification
  //   - The top-level sequence of naturals should be in sorted order
  //   - Their corresponding containers must be valid
  predicate Valid(bmap: RBitmapModel) {
    var (topChunks, containers) := unzip(bmap);
    0 <= |bmap| <= Exp(2, 16)
      && (forall i, j :: 0 <= i < j < |bmap| ==> topChunks[i] < topChunks[j])
      && forall c :: c in containers ==> C.Valid(c)
  }

  /*
  More information: https://dafny.org/dafny/VerificationOptimization/VerificationOptimization
  We declare the `Elements` function opaque: this makes the body of `Elements`
  opaque in proof call sites. This hugely speeds up verification, as the SMT solver does not
  need to check the body, which contains a set comprehension and a recursive call. Unrolling
  the definition is hugely expensive, and unnecessary in most calculational proofs.
  When we do need to use this definition, the statement `reveal Elements()` is inserted
  to use the definition in a proof step.
  As of Dafny 4.7, this seems to no longer be necessary; verification 
  doesn't time out without the opaque declaration
  */
  function Elements(bmap: RBitmapModel): set<nat32> {
    if bmap == []
    then {}
    else 
      var (idx, container) := bmap[0];
      (set x | x in container.elems :: ElemFromChunks(idx, x)) + Elements(bmap[1..])
  }

  /* Helper functions for operating on the model
      
  */
  function TopChunks(bmap: RBitmapModel): seq<nat16> {
    unzip(bmap).0
  }

  function Containers(bmap: RBitmapModel): seq<C.Container> {
    unzip(bmap).1
  }

  
  predicate NoRunsContainer(bmap: RBitmapModel) {
    forall c :: c in Containers(bmap) ==> !c.RunsModel?
  }

  function TopChunkIndex(topChunk: nat16, bmap: RBitmapModel): nat
    requires topChunk in TopChunks(bmap)
    requires Valid(bmap)
  {
    var (k, _) := first(bmap);
    if k == topChunk then 0 else 1 + TopChunkIndex(topChunk, bmap[1..])
  }

  function InsertPosition(topChunk: nat16, bmap: RBitmapModel): nat
    requires topChunk !in TopChunks(bmap)
    requires Valid(bmap)
    ensures var idx := InsertPosition(topChunk, bmap);
            var topChunks := TopChunks(bmap);
            0 <= idx <= |bmap| &&
            (forall i :: 0 <= i < idx ==> topChunks[i] < topChunk) &&
            (forall i :: idx <= i < |bmap| ==> topChunk < topChunks[i])
  {
    FindInsertIndex(topChunk, unzip(bmap).0)
  }

  /*
  Lemmas
  */

  /*********************/
  // Valid LEMMAS      //
  /*********************/
  lemma ValidSplitOffFirst(bmap: RBitmapModel)
    requires |bmap| > 0
    requires Valid(bmap)
    ensures Valid([first(bmap)])
    ensures Valid(tail(bmap))
  {
    var (topChunks, containers) := unzip(tail(bmap));
    P.SplitOffBottomStrictOrder(TopChunks(bmap));
    assert forall i, j :: 0 <= i < j < |tail(bmap)| ==> topChunks[i] < topChunks[j];
  }

  /*********************/
  // Elements LEMMAS   //
  /*********************/

  // Assoc-sym of Elements
  lemma ElementsSymmetric(b1: RBitmapModel, b2: RBitmapModel)
    ensures Elements(b1 + b2) == Elements(b2 + b1)
  {
    calc {
      Elements(b1 + b2);
    =={ ElementsSplit(b1, b2); }
      Elements(b1) + Elements(b2);
    =={ ElementsSplit(b2, b1); }
      Elements(b2 + b1);
    }

  }

  lemma ElementsAssociative(b1: RBitmapModel, b2: RBitmapModel, b3: RBitmapModel)
    ensures Elements((b1 + b2) + b3) == Elements(b1 + (b2 + b3))
  {
    ElementsSplit(b1 + b2, b3);
    ElementsSplit(b1, b2);
    ElementsSplit(b2, b3);
    ElementsSplit(b1, b2 + b3);
  }

  // The validity condition isn't necessary to prove
  // this lemma
  lemma ElementsSplit(b1: RBitmapModel, b2: RBitmapModel)
    // requires Valid(b1) && Valid(b2)
    ensures Elements(b1 + b2) == Elements(b1) + Elements(b2)
  {
    if b1 == [] {
      calc {
        Elements([] + b2);
      =={ assert [] + b2 == b2; }
        Elements(b2);
      =={} // reveal Elements();
        Elements([]) + Elements(b2);
      }
    } else if b2 == [] {
      calc {
        Elements(b1 + []);
      =={ assert b1 + [] == b1; }
        Elements(b1);
      =={} // reveal Elements();
        Elements(b1) + Elements([]);
      }
    } 
    else {
      var (idx, container) := (b1 + b2)[0];
      calc {
        Elements(b1 + b2);
      =={} // reveal Elements();
        (set x | x in container.elems :: ElemFromChunks(idx, x)) + Elements((b1 + b2)[1..]);
      =={ assert (b1 + b2)[1..] == b1[1..] + b2; }
        (set x | x in container.elems :: ElemFromChunks(idx, x)) + Elements((b1[1..] + b2));
      =={ // This assertion needs to be proved if we have the validity preconditions
          //  assert Valid(b1[1..]);
          ElementsSplit(b1[1..], b2); } // Figures out automatic induction
        (set x | x in container.elems :: ElemFromChunks(idx, x)) + Elements(b1[1..]) + Elements(b2);
      =={} // reveal Elements();
        Elements(b1) + Elements(b2);
      }
    }
  }

  lemma ElementsSplitSingleton(b1: RBitmapModel, single: (nat16, C.Container))
    ensures Elements(b1 + [single]) == Elements(b1) + Elements([single])
  {
    ElementsSplit(b1, [single]);
  }

  /*********************/
  // INSERT LEMMAS     //
  /*********************/

  lemma FullBmapImpliesMembership(topChunk: nat16, bmap: RBitmapModel)
    requires Valid(bmap)
    requires |bmap| == Exp(2, 16)
    ensures topChunk in TopChunks(bmap)
  {
    var topChunks := TopChunks(bmap);
    P.StrictOrderingPerm(Exp(2, 16), topChunks);
    assert topChunks[topChunk] == topChunk;
    assert topChunk in topChunks;
  }

  lemma TopChunkMissingImpliesNonFull(topChunk: nat16, bmap: RBitmapModel)
    requires Valid(bmap)
    requires topChunk !in TopChunks(bmap)
    ensures |bmap| < Exp(2, 16)
  {
    // By contrapositive
    if |bmap| == Exp(2, 16) {
      FullBmapImpliesMembership(topChunk, bmap);
    }
  }

  lemma InsertPreservesValidity(topChunk: nat16, botChunk: nat16, idx: nat, bmap: RBitmapModel)
    requires topChunk !in TopChunks(bmap)
    requires |bmap| < Exp(2, 16)
    requires Valid(bmap)
    requires idx == InsertPosition(topChunk, bmap)
    ensures var newBmap := bmap[0..idx] + [(topChunk, C.SingletonContainer(botChunk))] + bmap[idx..];
            Valid(newBmap)
  {

  }

  lemma InsertCorrect(x: nat32, bmap: RBitmapModel)
    requires Valid(bmap)
    requires NoRunsContainer(bmap)
    ensures Elements(InsertRBitmapModel(x, bmap))
            == Elements(bmap) + {x}
  {
    
  }

  /*********************/
  // UNION LEMMAS      //
  /*********************/

  // Elements(b1) + Elements(b2) == Elements(UnionRBitmap(b1, b2))
  // Elements([singleton]) + Elements(b1[1..]) + Elements(b2[1..]) == Elements(b1) + Elements(b2)
  lemma UnionSameTopChunkElements(topChunk: nat16, container1: C.Container, container2: C.Container)
    requires C.Valid(container1) && C.Valid(container2)
    ensures Elements([(topChunk, container1)]) + Elements([(topChunk, container2)]) ==
            Elements([(topChunk, C.UnionContainers(container1, container2))])
  {
    calc {
      Elements([(topChunk, container1)]) + Elements([(topChunk, container2)]);
    =={ ElementsSplit([(topChunk, container1)], [(topChunk, container2)]); }
      Elements([(topChunk, container1)] + [(topChunk, container2)]);
    == // by defn. of union
      Elements([(topChunk, C.UnionContainers(container1, container2))]);
    }
  }

/*
lemma ValidUnionConcat(topChunk1: nat16, c1: C.Container, c2: C.Container,
                       b1: RBitmapModel, b2: RBitmapModel)
  decreases |b1| + |b2|
  requires C.Valid(c1) && C.Valid(c2)
  requires |b1| > 0 && |b2| > 0
  requires Valid(b1[1..]) && Valid(b2[1..])
  requires Valid([(topChunk1, C.UnionContainers(c1, c2))])
  requires Valid(UnionRBitmap(b1[1..], b2[1..]))
  requires forall topChunk :: topChunk in TopChunks(b1[1..]) && 
    topChunk in TopChunks(b2[1..]) ==>
    topChunk1 < topChunk
  ensures var thisContainer := [(topChunk1, C.UnionContainers(c1, c2))];
          var restUnion := UnionRBitmap(b1[1..], b2[1..]);
  Valid(thisContainer + restUnion)
*/

///////////////////////////////////////////////////////
  
  /*********************/
  // MODULE DEFINITIONS //
  /*********************/

  predicate IsEmptyRBitmapModel(bmap: RBitmapModel)
  {
    |bmap| == 0
  }

  function InitBitmapModel(): RBitmapModel
    ensures IsEmptyRBitmapModel(InitBitmapModel())
  {
    []
  }

  predicate InRBitmapModel(x: nat32, bmap: RBitmapModel)
    requires Valid(bmap)
  {
    var (topChunk, botChunk) := ChunksFromElem(x);
    var (topChunks, containers) := unzip(bmap);
    var topChunkExists := topChunk in topChunks;
    assert topChunkExists ==> 
      exists i :: 0 <= i < |topChunks| && topChunks[i] == topChunk;
    topChunkExists &&
      exists i :: 0 <= i < |topChunks| && topChunks[i] == topChunk && C.InContainer(botChunk, containers[i])
  }

  function InsertRBitmapModel(x: nat32, bmap: RBitmapModel): RBitmapModel
    requires Valid(bmap)
    requires NoRunsContainer(bmap)
    ensures var newRBitmap := InsertRBitmapModel(x, bmap);
            Valid(newRBitmap) && InRBitmapModel(x, newRBitmap)
    ensures Elements(InsertRBitmapModel(x, bmap)) == 
            Elements(bmap) + {x}
  {
    var (topChunk, botChunk) := ChunksFromElem(x);
    // Alerting Dafny to this relation makes the postcondition verify quickly
    // Since this is used by both insert functions and is used
    // in the definition of Elements 
    assert x == ElemFromChunks(topChunk, botChunk);
    var (topChunks, containers) := unzip(bmap);
    var topChunkExists := topChunk in topChunks;
    if topChunkExists
    then
      InsertExistingContainer(topChunk, botChunk, bmap)
    else
      TopChunkMissingImpliesNonFull(topChunk, bmap);
      LinearInsertTopChunk(topChunk, botChunk, bmap)
  }

  function LinearInsertTopChunk(topChunk: nat16, botChunk: nat16, bmap: RBitmapModel): RBitmapModel
    requires topChunk !in TopChunks(bmap)
    requires |bmap| < Exp(2, 16)
    requires Valid(bmap)
    ensures var newModel := LinearInsertTopChunk(topChunk, botChunk, bmap);
            Valid(newModel) &&
            InRBitmapModel(ElemFromChunks(topChunk, botChunk), newModel) &&
            Elements(newModel) == Elements(bmap) + {ElemFromChunks(topChunk, botChunk)}
  {
    var idx := InsertPosition(topChunk, bmap);
    InsertPreservesValidity(topChunk, botChunk, idx, bmap);
    var singleton := [(topChunk, C.SingletonContainer(botChunk))];
    var newModel := bmap[0..idx] + singleton + bmap[idx..];
    assert Valid(newModel);
    assert newModel[idx] == (topChunk, C.SingletonContainer(botChunk));
    assert InRBitmapModel(ElemFromChunks(topChunk, botChunk), newModel);
    calc {
      Elements(newModel);
    =={ ElementsAssociative(bmap[0..idx], singleton, bmap[idx..]); }
      Elements(bmap[0..idx] + (singleton + bmap[idx..]));
    =={ ElementsSplit(bmap[0..idx], singleton + bmap[idx..]); }
      Elements(bmap[0..idx]) + Elements(singleton + bmap[idx..]);
    =={ ElementsSymmetric(singleton, bmap[idx..]); }
      Elements(bmap[0..idx]) + Elements(bmap[idx..] + singleton);
    =={ ElementsSplit(bmap[0..idx], bmap[idx..] + singleton);
        ElementsAssociative(bmap[0..idx], bmap[idx..], singleton); }
      Elements(bmap[0..idx] + bmap[idx..] + singleton);
    =={ assert bmap[0..idx] + bmap[idx..] == bmap; }
      Elements(bmap + singleton);
    =={ ElementsSplit(bmap, singleton); }
      Elements(bmap) + Elements(singleton);
    =={ // reveal Elements();
        assert Elements(singleton) == {ElemFromChunks(topChunk, botChunk)}; }
      Elements(bmap) + {ElemFromChunks(topChunk, botChunk)};
    }
    newModel
  }

  /*
  Verification metrics:
  Without opaque Elements function:
  """
  Verification performance metrics for function InsertExistingContainer:

  Total resource usage: 26.4M RU ⚠
  Only one assertion batch containing 74 assertions.
  """
  With opaque Elements function:
  """
  Verification performance metrics for function InsertExistingContainer:

  Total resource usage: 10.7M RU ⚠
  Only one assertion batch containing 74 assertions.
  """
  */
  function InsertExistingContainer(topChunk: nat16, botChunk: nat16, bmap: RBitmapModel): RBitmapModel
    requires topChunk in TopChunks(bmap)
    requires NoRunsContainer(bmap)
    requires Valid(bmap)
    ensures var newModel := InsertExistingContainer(topChunk, botChunk, bmap);
            Valid(newModel) &&
            InRBitmapModel(ElemFromChunks(topChunk, botChunk), newModel) &&
            Elements(newModel) == Elements(bmap) + {ElemFromChunks(topChunk, botChunk)}
  {
    var topChunkIndex := Find(topChunk, TopChunks(bmap));
    var container := bmap[topChunkIndex].1;
    var insertContainerElem := (topChunk, C.InsertContainer(botChunk, container));
    var insertedBmap := bmap[topChunkIndex := insertContainerElem];
    ghost var singleton := [(topChunk, C.SingletonContainer(botChunk))];
    assert insertedBmap[topChunkIndex].1.elems == container.elems + {botChunk};
    assert insertedBmap == bmap[..topChunkIndex] + [insertContainerElem] + bmap[topChunkIndex+1..];
    calc {
      Elements([insertContainerElem]);
    =={} // reveal Elements();
      var c := C.InsertContainer(botChunk, container);
      set x | x in c.elems :: ElemFromChunks(topChunk, x);
    == // Split off botChunk
      ({ElemFromChunks(topChunk, botChunk)}) + (set x | x in container.elems :: ElemFromChunks(topChunk, x));
    =={} // reveal Elements();
      ({ElemFromChunks(topChunk, botChunk)}) + Elements([bmap[topChunkIndex]]);
    }
    calc {
      Elements(insertedBmap);
    == // defn insertedBmap by assertion
      Elements(bmap[..topChunkIndex] + [insertContainerElem] + bmap[topChunkIndex+1..]);
    =={ ElementsSplit(bmap[..topChunkIndex] + [insertContainerElem], bmap[topChunkIndex+1..]); }
      Elements(bmap[..topChunkIndex] + [insertContainerElem]) + Elements(bmap[topChunkIndex+1..]);
    =={ ElementsSplitSingleton(bmap[..topChunkIndex], insertContainerElem); }
        (Elements(bmap[..topChunkIndex]) 
      + Elements([insertContainerElem]))
      + Elements(bmap[topChunkIndex+1..]);
    =={ assert Elements([insertContainerElem]) == 
           ({ElemFromChunks(topChunk, botChunk)}) + Elements([bmap[topChunkIndex]]);
      }
      Elements(bmap[..topChunkIndex]) 
      + ({ElemFromChunks(topChunk, botChunk)}) + Elements([bmap[topChunkIndex]])
      + Elements(bmap[topChunkIndex+1..]);
    =={ ElementsSplit(bmap[..topChunkIndex], [bmap[topChunkIndex]]);
        ElementsSplit(bmap[..topChunkIndex] + [bmap[topChunkIndex]], bmap[topChunkIndex+1..]); }
      Elements(bmap[..topChunkIndex] + [bmap[topChunkIndex]] + bmap[topChunkIndex+1..])
      + ({ElemFromChunks(topChunk, botChunk)});
    =={ assert bmap == bmap[..topChunkIndex] + [bmap[topChunkIndex]] + bmap[topChunkIndex+1..]; }
      Elements(bmap) + {ElemFromChunks(topChunk, botChunk)};
    }
    insertedBmap
  }

  /*
  Elements(b1[1..]) + Elements(b2[1..]) + [singleton]
  == Elements([(topChunk1, C.UnionContainers(container1, container2))] + UnionRBitmap(b1[1..], b2[1..]))
  */

  function UnionRBitmap(b1: RBitmapModel, b2: RBitmapModel): RBitmapModel
    requires Valid(b1) && Valid(b2)
    ensures var bUnion := UnionRBitmap(b1, b2);
      Valid(bUnion) &&
      Elements(bUnion) == Elements(b1) + Elements(b2)
  {
    if b1 == [] then b2
    else if b2 == [] then b1
    else
      var (topChunk1, container1) := b1[0];
      var (topChunk2, container2) := b2[0];
      if topChunk1 == topChunk2 then
        var thisContainer := [(topChunk1, C.UnionContainers(container1, container2))];
        assert Valid(thisContainer);
        ValidSplitOffFirst(b1); ValidSplitOffFirst(b2);
        var restUnion := UnionRBitmap(b1[1..], b2[1..]);
        assert Valid(restUnion);
        var unionBmap := thisContainer + restUnion;
        // We can show that Elements(unionBmap) == Elements(b1) + Elements(b2) with a calc:
        /*
        calc {
          Elements(unionBmap);
        == // defn. unionBmap
          Elements(thisContainer + restUnion);
        =={ ElementsSplit(thisContainer, restUnion); }
          Elements(thisContainer) + Elements(restUnion);
        =={ assert Elements(restUnion) == Elements(b1[1..]) + Elements(b2[1..]); }
          Elements(thisContainer) + Elements(b1[1..]) + Elements(b2[1..]);
        =={ UnionSameTopChunkElements(topChunk1, container1, container2); }
          Elements([b1[0]]) + Elements([b2[0]]) + Elements(b1[1..]) + Elements(b2[1..]);
        ==// Singleton split Elements
          Elements(b1) + Elements(b2);
        }
        */
        /*
        Here, we want to show Valid(unionBmap), which is Valid(thisContainer + restUnion).
        The two conditions that Dafny requires help with are:
        1. (forall i, j :: 0 <= i < j < |unionBmap| ==> topChunks[i] < topChunks[j]), 
            i.e. top-level chunks ordering are preserved
        2. 0 <= |unionBmap| <= Exp(2, 16), i.e. the top-level bitmap cardinality is within 2^16
        (Note that for forall c :: c in containers ==> C.Valid(c), Dafny is able to prove this trivially)

        For 1. we just need to show that `topChunk1`, which is in `thisContainer`, is less than elements
        in the two separate bitmaps that we are applying the union function recursively on.

        For 2. it is not obvious to Dafny, because it doesn't know that `topChunk1` doesn't exist in
        `restUnion`. By stating this fact and applying the lemma `TopChunkMissingImpliesNonFull`,
        Dafny can then reason that the resulting union cardinality won't exceed 2^16.
        */
        assert [topChunk1] + TopChunks(b1[1..]) == TopChunks(b1);
        assert [topChunk1] + TopChunks(b2[1..]) == TopChunks(b2);
        // assert forall i :: i in TopChunks(b1[1..]) ==> topChunk1 < i;
        // assert forall i :: i in TopChunks(b2[1..]) ==> topChunk1 < i;
        // assert forall i :: i in TopChunks(restUnion) ==> topChunk1 < i;
        // P.InsertLeastElementStrictOrder(topChunk1, TopChunks(restUnion));
        // assert TopChunks(unionBmap) == [topChunk1] + TopChunks(restUnion);
        // assert forall c :: c in  Containers(thisContainer + restUnion) ==> C.Valid(c);
        assert topChunk1 !in TopChunks(restUnion);
        TopChunkMissingImpliesNonFull(topChunk1, restUnion);
        assert 0 <= |unionBmap| <= Exp(2, 16);
        unionBmap
      /*
      The other two cases where the key is not equal follows the same proof structure as above;
      we only need to alert Dafny that b1/b2 do not have duplicates, and selecting a topChunk from
      either would satisfy the validity predicate on the size of the resulting bitmap.
      That is, 0 <= |unionBmap| <= Exp(2, 16).
      */
      else if topChunk1 < topChunk2 then 
        ValidSplitOffFirst(b1);
        var restUnion := UnionRBitmap(b1[1..], b2);
        var unionBmap := [b1[0]] + restUnion;
        P.StrictOrderImpliesNoDuplicateSorted(TopChunks(b1));
        assert topChunk1 !in TopChunks(b1[1..]);
        TopChunkMissingImpliesNonFull(topChunk1, restUnion);
        assert 0 <= |unionBmap| <= Exp(2, 16);
        unionBmap
      else
        assert topChunk2 < topChunk1;
        ValidSplitOffFirst(b2);
        var restUnion := UnionRBitmap(b1, b2[1..]);
        var unionBmap := [b2[0]] + restUnion;
        P.StrictOrderImpliesNoDuplicateSorted(TopChunks(b2));
        assert topChunk2 !in TopChunks(b2[1..]);
        TopChunkMissingImpliesNonFull(topChunk2, restUnion);
        assert 0 <= |unionBmap| <= Exp(2, 16);
        unionBmap
  }
}