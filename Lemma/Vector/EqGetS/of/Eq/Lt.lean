import Lemma.Vector.EqLengthS.of.SEq
import Lemma.Algebra.All_EqGetS.of.Eq
open Algebra Vector


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


@[main]
private lemma heter
  {a : List.Vector α n}
  {b : List.Vector α m}
  {i : ℕ}
-- given
  (h_i : i < n)
  (h : a ≃ b) :
-- imply
  have h_length := EqLengthS.of.SEq h
  have h_length : n = m := by
    simp [List.Vector.length] at h_length
    assumption
  have : i < m := by rwa [← h_length]
  a[i] = b[i] := by
-- proof
  intro h_length h_length h_i
  -- simp [EQ.eq] at h
  simp [GetElem.getElem]
  have hi : i < a.val.length := by
      simp_all
  have hi : i < b.val.length := by
    simp_all
  have h : a.val[i] = b.val[i] := by
    have h := All_EqGetS.of.Eq h
    specialize h ⟨i, by simp_all⟩
    aesop
  simp [List.Vector.get]
  simp_all


-- created on 2025-07-06
