import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.RamificationInertia.ResidueGenerator


variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
/--
[adjoin_singleton_two_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RamificationInertia/ResidueGenerator.lean)
-/
@[path]
private lemma adjoin_singleton_two_eq_top :
  Algebra.adjoin ℤ ({(2 : ℤ)} : Set ℤ) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  have h : algebraMap ℤ ℤ x ∈ Algebra.adjoin ℤ ({(2 : ℤ)} : Set ℤ) :=
    Subalgebra.algebraMap_mem _ x
  simpa using h


-- created on 2026-10-23
