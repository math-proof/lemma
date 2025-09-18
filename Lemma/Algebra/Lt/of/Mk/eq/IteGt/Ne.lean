import Lemma.Algebra.Le.of.Mk.eq.IteGt
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Logic.EqUFnS.of.Eq
open Algebra Logic


@[main]
private lemma main
  [LinearOrder α]
  {a b a' b' : α}
-- given
  (h₀ : a ≠ b)
  (h₁ : (⟨a', b'⟩ : α × α) = if a > b then
    ⟨b, a⟩
  else
    ⟨a, b⟩) :
-- imply
  a' < b' := by
-- proof
  have := Le.of.Mk.eq.IteGt h₁
  apply Lt.of.Le.Ne _ this
  by_contra h
  split at h₁ <;>
  ·
    rw [h] at h₁
    have h_1 := EqUFnS.of.Eq h₁ Prod.fst
    simp at h_1
    have h_2 := EqUFnS.of.Eq h₁ Prod.snd
    simp at h_2
    simp_all


-- created on 2025-06-20
