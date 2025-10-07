import Lemma.Bool.NotOr.is.AndNotS
import Lemma.Bool.NotAnd.is.OrNotS
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.NotLt.is.Ge
import Lemma.Algebra.Ge_0.Ge_0.is.OrGeS_0.OrAndS
import Lemma.Bool.AndAnd.is.And_And
open Algebra Bool


@[main, mp, mpr]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (x y : α) :
-- imply
  (x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) ∧ ¬(x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0) ↔ x ≥ 0 ∧ y ≥ 0 ∧ (x ≤ 0 ∨ y ≤ 0) := by
-- proof
  constructor
  ·
    intro ⟨h₁, h₀⟩
    rw [NotOr.is.AndNotS] at h₀
    rw [NotAnd.is.OrNotS, NotAnd.is.OrNotS] at h₀
    rw [NotGt.is.Le, NotGt.is.Le] at h₀
    rw [NotLt.is.Ge, NotLt.is.Ge] at h₀
    have h₁ := Ge_0.Ge_0.of.OrGeS_0.OrAndS h₀.right h₁
    aesop
  ·
    intro ⟨h₀, h₁, h₂⟩
    rw [NotOr.is.AndNotS]
    rw [NotAnd.is.OrNotS, NotAnd.is.OrNotS]
    rw [NotGt.is.Le, NotGt.is.Le]
    rw [NotLt.is.Ge, NotLt.is.Ge]
    rw [And.comm]
    rw [AndAnd.is.And_And]
    have := OrGeS_0.OrAndS.of.Ge_0.Ge_0 h₀ h₁
    aesop


-- created on 2025-04-19
