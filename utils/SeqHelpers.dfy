/*
 * This file includes code from deposit-sc-dafny
 * https://github.com/Consensys/deposit-sc-dafny/blob/master/src/dafny/smart/helpers/SeqHelpers.dfy
 * Licensed under the Apache License 2.0
 * Modified by Lucas Dutton to include functions `unzip`, `Find` and `FindInsertIndex`
 */

/**
  *  Provide useful lemmas on sequences.
  */
module SeqHelpers {
  /**
    * First element of a sequence.
    *  
    *  @param  p   A sequence of length >= 1.
    *  @returns    The first element.
    */
  function first<T>(p : seq<T>) : T
    requires 1 <= |p|
    ensures first(p) == p[0]
  {
    p[0]
  }

  /**
    * Tail  of a sequence.
    *  
    *  @param  p   A sequence of length >= 1.
    *  @returns    The tail (all but first element).
    */
  function tail<T>(p : seq<T>) : seq<T>
    requires 1 <= |p|
    ensures tail(p) == p[1..]
  {
    p[1..]
  }

  /**
    *  Initial prefix of a sequence.
    *  
    *  @param  p   A sequence of length >= 1.
    *  @returns    The sequence p minus the last element.
    */
  function init<T>(p : seq<T>) : seq<T>
    requires 1 <= |p|
    ensures |init(p)| == |p| - 1
    ensures init(p) ==  p[..|p| - 1]
    ensures init(p) < p
  {
    p[..|p| - 1]
  }

  /**
    *  Last element of a sequence.
    *  
    *  @param  p   A sequence of length >= 1.
    *  @returns    The last element of p.
    */
  function last<T>(p : seq<T>) : T
    requires 1 <= |p|
    ensures last(p) ==  p[|p| - 1]
  {
    p[|p| - 1]
  }

  /**
    *  k-Prefix of a sequence.
    *  
    *  @param  p   A sequence.
    *  @param  k   A integer between 0 and |p|.
    *  @returns    The sequence made of the first k elements of p.
    */
  function take<T>(p : seq<T>, k : nat) : seq<T>
    requires |p| >= k
    ensures |take(p, k)| == k
    ensures take(p, k) ==  p[..k]
    ensures take(p, k) <= p
    ensures k == |p| ==> take(p, k) == p
    ensures k < |p| ==> take(p, k) < p
  {
    p[..k]
  }

  /**
    *  Suffix of a sequence.
    *  
    *  @param  p   A sequence.
    *  @param  k   A integer between 0 and |p|.
    *  @returns    The sequence made of the last k - |p| elements of p.
    */
  function  drop<T>(p : seq<T>, k : nat) : seq<T>
    requires |p| >= k
    ensures |drop(p, k)| == |p| - k
    ensures drop(p, k) == p[k..]
  {
    p[k..]
  }

  /**
    *  Reverses a sequence.
    *  
    *  @param  p   A sequence.
    *  @returns    The sequence `p` in reverse order.
    */
  function reverse<T>(p: seq<T>) : seq<T>
    ensures |reverse(p)| == |p|
    ensures forall k:: 0 <= k < |p| ==> reverse(p)[|p| - 1 - k] == p[k]
    ensures forall k:: 0 <= k < |p| ==> reverse(p)[k] == p[|p| - 1 - k]
    decreases p
  {
    if |p| == 0 then
      []
    else
      reverse(tail(p)) + [first(p)]
  }

  function unzip<A, B>(xs: seq<(A, B)>): (seq<A>, seq<B>)
    ensures var res := unzip(xs);
            |res.0| == |res.1| == |xs| &&
            forall i :: 0 <= i < |xs| ==>
                          xs[i].0 == res.0[i] && xs[i].1 == res.1[i]
  {
    if xs == []
    then ([], [])
    else
      var xPair := first(xs);
      var xsPairRest := unzip(tail(xs));
      ([xPair.0] + xsPairRest.0, [xPair.1] + xsPairRest.1)
  }

  function Find(n: int, s: seq<int>): int
    requires n in s
    ensures var idx := Find(n, s);
            0 <= idx < |s| &&
            s[idx] == n
  {
    if s[0] == n then 0
    else 1 + Find(n, s[1..])
  }

  function FindInsertIndex(n: int, s: seq<int>): int
    requires forall i, j :: 0 <= i < j < |s| ==>
                              s[i] < s[j]
    requires n !in s
    ensures var idx := FindInsertIndex(n, s);
            0 <= idx <= |s| &&
            (forall i :: 0 <= i < idx ==> s[i] < n) &&
            (forall i :: idx <= i < |s| ==> s[i] > n)
  {
    if s == [] || s[0] > n
    then 0
    else
      assert s[0] < n;
      var tailSeq := s[1..];
      var forwardIdx := FindInsertIndex(n, tailSeq);

      assert s[0..forwardIdx+1] == [first(s)] + tailSeq[0..forwardIdx];
      assert s[forwardIdx+1..] == tailSeq[forwardIdx..];
      forwardIdx + 1
  }

  //  Useful lemmas on init, last, take and drop.
  lemma seqLemmas<T>(p : seq<T>)
    requires 1 <= |p|
    ensures p == init(p) + [last(p)]
    ensures p == [first(p)] + tail(p)
    ensures init(p) == take(p, |p| - 1)
    ensures [last(p)] == drop(p, |p| - 1)
    ensures [first(p)] == take(p, 1)
    ensures tail(p) == drop(p, 1)
    ensures p == take(p, |p|)
    ensures |p| >= 2 ==> init(tail(p)) == tail(init(p))
    ensures |p| >= 2 ==> last(tail(p)) == last(p)
    ensures |p| >= 1 ==> last(take(p, |p|)) == p[|p| - 1]
  {
    //  Thanks Dafny
  }

  //  Some standard lemmas combining drop, take, init, first, tail, last

  lemma seqIndexLemmas<T>(p : seq<T>, k : nat)
    requires 1 <= |p|
    requires 0 <= k <= |p|
    ensures k < |p| ==> take(p, k) == take(init(p), k)
    ensures 0 <= k < |init(p)| ==> p[k] == init(p)[k]
    ensures k >= 1 ==> tail(take(p, k)) == take(tail(p), k - 1)
    ensures k >= 1 ==> first(take(p, k)) == first(p)
    ensures k < |p| ==> init(drop(p, k)) == drop(init(p), k)
    ensures k < |p| ==> last(drop(p, k)) == last(p)
    ensures 1 <= k <= |p| ==> last(take(p, k)) == p[k - 1]
    ensures 1 <= k <= |p| ==> init(take(p, k)) == take(p, k - 1)
    // ensures 1 <= k <= |p| ==> init(drop(p, k)) == take(p, k - 1)

  {
    //  Thanks Dafny
  }

  lemma seqTakeTake<T>(p : seq<T>, k : nat, k' :nat)
    requires 0 <= k < k' <= |p|
    ensures take(take(p, k'), k) == take(p, k)
  {
    //  Thanks Dafny
  }

  lemma seqDropDrop<T>(p : seq<T>, k : nat, k' :nat)
    requires 0 <= k < k' <= |p|
    ensures drop(drop(p, k), k' - k) == drop(p, k')
  {
    //  Thanks Dafny
  }

  lemma prefixSeqs<T>(t: seq<T>, u : seq<T>, k : nat, l : nat)
    requires |t| == |u|
    requires 0 <= k <= l < |t|
    ensures t[..l] == u[..l] ==> t[..k] == u[..k]
    ensures take(t, l) == take(u, l) ==> take(t, k) == take(u, k)
    ensures t[..l] == u[..l] ==> t[k..l] == u[k..l]
  {
    //  Thanks Dafny
  }

  lemma suffixSeqs<T>(t: seq<T>, u : seq<T>, k : nat, l : nat)
    requires |t| == |u|
    requires 0 <= k <= l < |t|
    requires t[k..] == u[k..]
    ensures drop(t, k) == drop(u, k)
    ensures t[k..l] == u[k..l]
    ensures drop(take(t, l), k) == drop(take(u, l), k)
  {
    //  Thanks Dafny
  }

  lemma seqDropTake<T>(p : seq<T>, k : nat, k' :nat)
    requires 0 <= k <= k' <= |p|
    ensures drop(take(p, k'), k) == p[k..k']
    ensures p[..k'][k..] == p[k..k']
  {
    //  Thanks Dafny
  }

  lemma seqTakeDrop<T>(p : seq<T>, k : nat, k' :nat)
    requires 0 <= k <= k' <= |p|
    ensures take(drop(p, k),k' - k) == p[k..k']
    ensures p[k..][..k' - k] == p[k..k']
  {
    //  Thanks Dafny
  }

  lemma seqAppendLemmas<T>(p : seq<T>, a : T)
    requires |p| >= 1
    ensures init(p + [a]) == p
    ensures tail(p + [a]) == tail(p) + [a]
  {
    //  Thanks Dafny
  }

  lemma seqAppendIndexLemmas<T>(p : seq<T>, s : seq<T>, k : nat)
    requires k <= |p|
    ensures take(p + s, k) == take(p, k)
    ensures k < |p| ==> (p + s)[k] == p[k]
  {
    //  Thanks Dafny
  }
}