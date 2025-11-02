import Lemma.Vector.EqLengthS.of.SEq
import Lemma.Vector.All_EqGetS.of.SEq
open Vector


@[main]
private lemma main
  {a b : List.Vector α n}
  {i : ℕ}
-- given
  (h_i : i < n)
  (h : a = b) :
-- imply
  a[i] = b[i] := by
-- proof
  rw [h]


@[main]
private lemma nat
  {v : List.Vector α n}
  {i j : ℕ}
-- given
  (h_i : i < n)
  (h : i = j) :
-- imply
  v[i] = v[j] := by
-- proof
  simp [h]


-- created on 2025-07-06
