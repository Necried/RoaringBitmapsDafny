// Reference: https://leino.science/papers/krml275.html
/*
Contains function converting sets/maps to sequences; this is borrowed from the reference above.
In addition, functions for counting runs are defined here, which are used for run containers
in Roaring bitmaps.
*/

include "Permutations.dfy"
include "Utils.dfy"
include "SeqHelpers.dfy"

module CollectionHelpers {

  import P = Permutations
  import U = Utils
  import S = SeqHelpers

  function MapToSequence<A(!new),B>(m: map<A,B>, R: (A, A) -> bool): seq<(A,B)>
    requires IsTotalOrder(R)
  {
    var keys := SetToSequence(m.Keys, (a,a') => R(a, a'));
    seq(|keys|, i requires 0 <= i < |keys| => (keys[i], m[keys[i]]))
  }


  function SetToSequence<A(!new)>(s: set<A>, R: (A, A) -> bool): seq<A>
    requires IsTotalOrder(R)
    ensures var q := SetToSequence(s, R);
            forall i :: 0 <= i < |q| ==> q[i] in s
  {
    if s == {} then [] else
    ThereIsAMinimum(s, R);
    var x :| x in s && forall y :: y in s ==> R(x, y);
    [x] + SetToSequence(s - {x}, R)
  }

  lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A, A) -> bool)
    requires s != {} && IsTotalOrder(R)
    ensures exists x :: x in s && forall y :: y in s ==> R(x, y)
  {
    var x :| x in s;
    if s == {x} {
      assert forall y :: y in s ==> x == y;
    } else {
      var s' := s - {x};
      assert s == s' + {x};
      ThereIsAMinimum(s', R);
      var z :| z in s' && forall y :: y in s' ==> R(z, y);
      if
      case R(z, x) =>
        // prove z is the minimum not just of s', but of s
        forall y | y in s
          ensures R(z, y)
        {
          assert x == y || y in s';
        }
      case R(x, z) =>
        forall y | y in s
          ensures R(x, y)
        {
          assert y in s' ==> R(z, y);
        }
        // prove x is the minimum of s
        // ...
    }
  }

  /*
  Leino's presentation uses antisymmetry as an assumption; but we can make this more precise,
  as sets only contain unique elements. We thus include the extra condition in the
  let-such-that (definite assignment) statement that `y != x`; the corresponding
  lemma invoked has been changed to reflect that.
  This implies we can change the general case to use a strict total order
  (instead of a total partial order as defined currently in the `IsTotalOrder` predicate)
  */
  function IntSetToSequence(s: set<int>): seq<int>
    ensures var q := IntSetToSequence(s);
            forall i :: 0 <= i < |q| ==> q[i] in s
  {
    if s == {} then [] else
    ThereIsAMinimumInt(s);
    var x :| x in s && forall y :: y in s && y != x ==> x < y;
    [x] + IntSetToSequence(s - {x})
  }

  lemma ThereIsAMinimumInt(s: set<int>)
    requires s != {}
    ensures exists x :: x in s && forall y :: y in s && y != x ==> x < y && !(y < x)
  {
    var x :| x in s;
    if s == {x} {

    } else {
      // The minimum in s might be x, or it might be the minimum
      // in s - {x}. If we knew the minimum of the latter, then
      // we could compare the two.
      // Let's start by giving a name to the smaller set:
      var s' := s - {x};
      // So, s is the union of s' and {x}:
      assert s == s' + {x};
      // The following lemma call establishes that there is a
      // minimum in s'.
      ThereIsAMinimumInt(s');
    }
  }

  lemma IntSetToSequenceIsUnique(s: set<nat>)
    ensures var q := IntSetToSequence(s);
            P.UniqueSeq(q)
  {
    // Dafny is smart
  }

  ghost predicate IsTotalOrder<A(!new)>(R: (A, A) -> bool) {
    // connexity
    && (forall a, b :: R(a, b) || R(b, a))
       // antisymmetry
    && (forall a, b :: R(a, b) && R(b, a) ==> a == b)
       // transitivity
    && (forall a, b, c :: R(a, b) && R(b, c) ==> R(a, c))
  }

  function SplitRun(s: seq<nat>): nat
    requires P.StrictOrderSortedSeq(s)
    ensures var n := SplitRun(s);
            0 <= n <= |s| &&
            (n < |s| - 1 ==> s[n + 1] > s[n] + 1) &&
            forall i :: 0 <= i < n - 1 ==> s[i] + 1 == s[i + 1]
  {
    if s == [] then 0
    else if |s| == 1 then 1
    else if s[0] + 1 == s[1]
    then
      1 + SplitRun(s[1..])
    else
      0
  }

  /*
  Determines if the given adjacent elements are increasing by exactly 1.
  This is used as a pseudo "count" function; if the elements satisfy
  the increasing condition, we return 0 as we do not need to increment
  the number of runs
  */
  function RunDelta(s_i: int, s_iprev: int): nat
  {
    if s_i != s_iprev + 1
    then 1
    else 0
  }

  /*
  Counts the number of runs in a sequence
  */
  function CountRuns(s: seq<int>): int
    requires P.StrictOrderSortedSeq(s)
  {
    if s == [] then 0
    else if |s| == 1 then 1
    else
      1 + U.Sum(seq(|s| - 2, i requires 0 <= i < |s| - 2 => RunDelta(s[i+1], s[i])))
  }

  /*
  Counts the number of runs of a set of integers; by first converting to a
  sequence and counting the runs there
  */

  function CountRunsSet(s: set<nat>): nat
    /*
      ensures var seqS := IntSetToSequence(s);
              var n := CountRuns(seqS);
        n == CountRuns(seqS)
    */
  {
    var seqS := IntSetToSequence(s);
    IntSetToSequenceIsUnique(s);
    var seqSorted := SortUniqueSeq(seqS);
    SortingUniqueSeqIsSorted(seqS);
    P.NoDuplicateSortedImpliesStrictOrder(seqSorted);
    assert P.StrictOrderSortedSeq(seqSorted);
    CountRuns(seqSorted)
  }

  lemma SplitRunDelta(s: seq<nat>)
    requires P.StrictOrderSortedSeq(s)
    ensures var n := SplitRun(s);
            forall i {:trigger RunDelta(i, i - 1)} :: 0 < i < n ==> RunDelta(i, i - 1) == 0
  {
    // Dafny is smart
  }

  function SortUniqueSeq(s: seq<int>): seq<int>
    requires P.UniqueSeq(s)
    ensures var v := SortUniqueSeq(s);
            multiset(s) == multiset(v) &&
            P.SortedSeq(v)
  {
    if s == [] then []
    else
      S.seqLemmas(s);
      P.UniqueMultisetImpliesUniqueElements(s);
      assert multiset(s) - multiset([S.first(s)]) == multiset(S.tail(s));
      assert P.UniqueSeq(S.tail(s));
      var n := S.first(s);
      var s' := SortUniqueSeq(S.tail(s));
      P.UniqueMultisetImpliesUniqueElements(s');
      var v := Insert(n, s');
      InsertPreservesElements(n, s');
      v
  }

  function Insert(n: int, s: seq<int>): seq<int>
    requires P.SortedSeq(s)
    requires P.NoDuplicateSeq(s)
    ensures var v := Insert(n, s);
            n in v &&
            P.SortedSeq(v)
  {
    if s == [] then [n]
    else if s[0] < n then // s[0]
      S.seqLemmas(s);
      var s' := Insert(n, S.tail(s));
      var v := [s[0]] + s';
      assert forall j :: 0 <= j < |s'| ==> s[0] < s'[j];
      v
    else
      [n] + s
  }

  lemma InsertPreservesElements(n: int, s: seq<int>)
    requires P.SortedSeq(s)
    requires P.NoDuplicateSeq(s)
    ensures var v := Insert(n, s);
            multiset(s + [n]) == multiset(v)
  {
    if s == [] {}
    else {
      if s[0] < n {
        S.seqLemmas(s);
        InsertPreservesElements(n, s[1..]);
      } else {
      }
    }
  }

  /*
  lemma LeastElementFront(n: int, s: seq<int>)
    requires P.SortedSeq(s)
    requires forall e :: e in s ==> n <= e
    ensures P.SortedSeq([n] + s) 
  {
    if s == [] {
    } else {
      var i :| 0 <= i < |s|;
      assume n <= s[i];
      assert s == s[..i] + [s[i]] + s[i..];
      LeastElementFront(n, s[..i] + s[i..]);
    }
  }
  */

  lemma SortingUniqueSeqIsSorted(s: seq<int>)
    requires P.UniqueSeq(s)
    ensures P.UniqueSeq(SortUniqueSeq(s))
  {
    // Dafny is smart
  }

  method Test() {
    assert IntSetToSequence({1, 2}) == [1] + IntSetToSequence({2});
    assert IntSetToSequence({1, 2}) == [1, 2];
  }
}

