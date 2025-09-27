import Lemma.Logic.EqUFnS.of.Eq
open Logic


@[main, comm 1]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h_eq : a.val = b.val) :
-- imply
  have h : List.Vector α n = List.Vector α m := by
    have := EqUFnS.of.Eq h_eq List.length
    simp at this
    rw [this]
  cast h a = b := by
-- proof
  intro h
  let ⟨a, ha⟩ := a
  let ⟨b, hb⟩ := b
  simp at h_eq
  simp [h_eq.symm]
  simp_all
  aesop



-- created on 2025-05-23
