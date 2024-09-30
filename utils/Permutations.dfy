include "Utils.dfy"
include "SeqHelpers.dfy"

// NOT USED
// Reference: https://dl-acm-org.libaccess.lib.mcmaster.ca/doi/pdf/10.1145/3464971.3468422
// Using Dafny to Solve the VerifyThis 2021 Challenges

module Permutations {
  import opened U = Utils
  import opened S = SeqHelpers

  predicate SortedSeq(s: seq<int>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  }

  predicate ValidPerm(n: nat, s: seq<nat>)
  {
    var mset := multiset(s);
    var basePerm := multiset(SortedSeqPerm(n));
    mset == basePerm
  }

  /*
  lemma UniqueElemsValidPerm(n: nat, s: seq<nat>)
    requires ValidPerm(n, s)
    ensures var mset := multiset(s);
            forall e :: e in s ==> mset[e] == 1
  {
    var sortedSeqPerm := SortedSeqPerm(n);
    var basePerm := multiset(sortedSeqPerm);
    assert ValidSortedPerm(sortedSeqPerm);
    assert forall e :: e in sortedSeqPerm ==> basePerm[e] == 1;
  }
  */

  predicate ValidSortedPerm(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> s[i] == i
  }

  predicate StrictOrderSortedSeq(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
  }

  predicate UniqueSeq(s: seq<int>) {
    var mset := multiset(s);
    forall e :: e in s ==> mset[e] == 1
  }

  predicate NoDuplicateSeq(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  function SortedSeqPerm(n: nat): seq<nat>
    ensures var s := SortedSeqPerm(n);
            ValidSortedPerm(s) && StrictOrderSortedSeq(s)
  {
    seq(n, i => i)
  }

  lemma NoDuplicateSortedImpliesStrictOrder(s: seq<int>)
    requires SortedSeq(s)
    requires UniqueSeq(s)
    ensures StrictOrderSortedSeq(s)
  {
    if |s| <= 1 {}
    else {
      // We're splitting the sequence on it's first element, thus
      // requiring some sequence lemmas to let Dafny know about some
      // relationships:
      S.seqLemmas(s);
      // Using the auxiliary lemma, we can then remove the first
      // element of the sequence and still preserve the
      // property of non-duplicates
      // The precondition of the lemma is satisfied via UniqueSeq(s)
      UniqueMultisetImpliesUniqueElements(s);
      var (x, rest) := (S.first(s),S.tail(s));
      assert x !in rest;
      // As with the auxiliary lemma, we're indirectly modifying
      // the multiset of the sequence. We show that multiset(rest)
      // is the same as removing the first element of the sequence
      // from multiset(s)
      var mset' := multiset(s) - multiset({x});
      assert mset' == multiset(rest);
      // assert mset' + multiset({x}) == multiset(s);
      NoDuplicateSortedImpliesStrictOrder(rest);
    }
  }

  lemma StrictOrderImpliesNoDuplicateSorted(s: seq<int>)
    requires StrictOrderSortedSeq(s)
    ensures SortedSeq(s)
    ensures NoDuplicateSeq(s)
  {

  }

  // WARNING: Not used, so there is no proof given
  // lemma {:axiom} UniqueElementsImpliesUniqueMultiset(s: seq<int>)
  //   requires NoDuplicateSeq(s)
  //   ensures UniqueSeq(s)

  lemma UniqueMultisetImpliesUniqueElements(s: seq<int>)
    requires UniqueSeq(s)
    ensures NoDuplicateSeq(s)
  {
    if |s| <= 1 {}
    else {
      // NOTE: Instead of the puzzling assertion below,
      // uncomment just use seqLemmas instead
      seqLemmas(s);
      // First, let's make Dafny aware of sequence splitting;
      // This is used to pass the precondition check of the inductive call
      // It's a bit mysterious, but I think Dafny uses this fact to
      // deduce that splitting a unique sequence ensures the
      // uniqueness of its parts
      // assert s == [s[0]] + s[1..];
      // Using the let-such-that operator, we pick an element at index `i`
      var i :| 0 <= i < |s|;
      var n := s[i];
      // We define the "leftover" multiset `mset'` and sequence `s'` respectively
      // We show how they are related to `mset` and `s` respectively
      var mset' := multiset(s) - multiset({n});
      var s' := s[..i] + s[i+1..];
      assert s == s[..i] + [n] + s[i+1..];
      assert mset' + multiset({n}) == multiset(s);
      // The inductive call happens here; Dafny can prove the precondition that
      // s' is unique, thanks to our work above
      UniqueMultisetImpliesUniqueElements(s');
      // Finally, using our defined auxillary lemma, we bring the fact that
      // inserting a unique element into a unique sequence preserves non-duplicates
      NoDupSplitIsNoDup(s', n, i);
    }
  }

  lemma NoDupSplitIsNoDup(s: seq<int>, n: int, i: int)
    requires NoDuplicateSeq(s)
    requires n !in s
    requires 0 <= i <= |s|
    ensures NoDuplicateSeq(s[..i] + [n] + s[i..])
  {

  }

  lemma SortedSeqPermElems(n: nat)
    ensures var s := SortedSeqPerm(n);
            forall i :: 0 <= i < n ==> s[i] == i
  {

  }

  lemma MembershipOfSortedSeqPerm(n: nat)
    ensures var s := SortedSeqPerm(n);
            forall i :: 0 <= i < n ==> i in s
  {
    var s := SortedSeqPerm(n);
    forall i | 0 <= i < n
      ensures i in s
    {
      assert s[i] == i;
    }
  }

  lemma MultisetSplit(s: seq<int>)
    requires |s| > 0
    ensures multiset(s) == multiset(s[..|s| - 1]) + multiset([s[|s| - 1]])
    ensures multiset(s) == multiset([s[0]]) + multiset(s[1..])
  {
    seqLemmas(s);
  }

  lemma UniqueElemsSortedSeqPerm(n: nat, s: seq<nat>)
    requires s == SortedSeqPerm(n)
    ensures UniqueSeq(s)
  {
    if n == 0 {}
    else {
      var mset := multiset(s);
      var msetN1 := multiset(s[..n - 1]);
      UniqueElemsSortedSeqPerm(n - 1, s[..n - 1]);
      // assert ValidSortedPerm(s);
      assert s[n - 1] == n - 1;
      // assert n - 1 !in s[..n - 1];
      // assert n - 1 !in multiset(s[..n - 1]);
      // assert n - 1 in mset;
      // assert forall e :: e in s[..n - 1] ==> msetN1[e] == 1;
      MultisetSplit(s);
      // assert mset == msetN1 + multiset([s[n - 1]]);
      // assert mset[n - 1] == 1;
      assert forall e :: e in s ==> mset[e] == 1;
    }
  }

  lemma StrictOrderingPerm(n: nat, s: seq<nat>)
    requires StrictOrderSortedSeq(s)
    requires n == |s|
    requires forall i :: 0 <= i < n ==> 0 <= s[i] < n
    ensures s == SortedSeqPerm(n)
  {
    if n <= 1 {}
    else {
      if s[n - 1] == n - 1 {
        StrictOrderingPerm(n - 1, s[..n - 1]);
        assert s == SortedSeqPerm(n);
      } else {
        StrictOrderingPerm(n - 1, s[..n - 1]);
        MembershipOfSortedSeqPerm(n - 1);
        assert s[n - 1] <= n - 2;
        assert n - 2 in s[..n - 1];
        assert !StrictOrderSortedSeq(s);
        assert false;
      }
    }
  }

  lemma SplitOffBottomStrictOrder(s: seq<nat>)
    requires StrictOrderSortedSeq(s)
    requires |s| > 0
    ensures StrictOrderSortedSeq(s[1..])
  {

  }

  lemma InsertLeastElementStrictOrder(n: int, s: seq<int>)
    requires StrictOrderSortedSeq(s)
    requires forall i :: i in s ==> n < i
    ensures StrictOrderSortedSeq([n] + s)
  {
    if s == [] {
    } else {
      assert forall i :: i in s ==> n < i;
      assert s[0] in s;
      assert n < s[0];
    }
  }

  method Test() {
    assert SortedSeqPerm(3) == [0, 1, 2];
  }

}