/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean -/

import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorem.GroupTheory.BurnsidePaqb.ClassSum.Part3
import Lemma.Nat.ConjClass.of.IsConj
import Theorem.GroupTheory.BurnsidePaqb.CentralCharacter.Part3
/-!
Central-character stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/CentralChar.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

section CentralScalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

open Classical in
/-- The ℤ-span of the central scalars, as a subalgebra. -/
noncomputable def scalarSubalg : Subalgebra ℤ ℂ where
  carrier := ↑(Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ))
  mul_mem' := by
    intro x y hx hy
    have hx' : x ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hx
    have hy' : y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hy
    suffices h : x * y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) from h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · intro z hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
      · intro w hw
        exact scalarGens_mul ρ z w (Finset.mem_coe.mp hz) (Finset.mem_coe.mp hw)
      · rw [mul_zero]
        exact Submodule.zero_mem _
      · intro a b ha hb iha ihb
        rw [mul_add]
        exact add_mem iha ihb
      · intro c b hb ih
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ ih
    · rw [zero_mul]
      exact Submodule.zero_mem _
    · intro a b ha hb iha ihb
      rw [add_mul]
      exact add_mem iha ihb
    · intro c a ha ih
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ ih
  one_mem' := one_mem_scalarSpan ρ
  add_mem' := by
    intro x y hx hy
    have hx' : x ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hx
    have hy' : y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := hy
    have h : x + y ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
      Submodule.add_mem _ hx' hy'
    exact h
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := by
    intro n
    have h1 : algebraMap ℤ ℂ n = n • (1 : ℂ) := by
      rw [Algebra.smul_def, mul_one]
    rw [h1]
    exact Submodule.smul_mem _ _ (one_mem_scalarSpan ρ)

end CentralScalar
end BurnsidePaqb
