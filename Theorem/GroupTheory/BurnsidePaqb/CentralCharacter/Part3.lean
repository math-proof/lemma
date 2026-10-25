/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean -/

import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorem.GroupTheory.BurnsidePaqb.ClassSum.Part3
import Lemma.Nat.ConjClass.of.IsConj
import Def.GroupTheory.BurnsidePaqb.CentralCharacter.Part2
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
theorem one_mem_scalarSpan : (1 : ℂ) ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self 1 _))

open Classical in
theorem scalar_mem_scalarSpan (l : ConjClasses G) :
    centralScalar ρ l ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) :=
  Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ l))))

open Classical in
/-- Generator-generator products stay in the span. -/
theorem scalarGens_mul (a b : ℂ) (ha : a ∈ scalarGens ρ) (hb : b ∈ scalarGens ρ) :
    a * b ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
  classical
  rw [scalarGens, Finset.mem_insert, Finset.mem_image] at ha hb
  rcases ha with rfl | ⟨l1, _, rfl⟩ <;> rcases hb with rfl | ⟨l2, _, rfl⟩
  · simpa using one_mem_scalarSpan ρ
  · simp only [one_mul]
    exact scalar_mem_scalarSpan ρ l2
  · simp only [mul_one]
    exact scalar_mem_scalarSpan ρ l1
  · rw [centralScalar_mul]
    apply sum_mem
    intro l _
    have hsmul : ∀ (n : ℕ) (x : ℂ), (n : ℂ) * x = (n : ℤ) • x := by
      intro n x
      exact (zsmul_eq_mul x n).symm
    rw [hsmul]
    exact Submodule.smul_mem _ _ (scalar_mem_scalarSpan ρ l)

end CentralScalar
end BurnsidePaqb
