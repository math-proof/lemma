/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Structure.RingTheory.GradedAlgebra.MultigradedFreeResolution
import Mathlib.LinearAlgebra.Dimension.Finite
import Lemma.Int.GradedAlgebra.FiniteHomogeneousGenerators
import Def.RingTheory.Polynomial.HilbertSyzygy
import Lemma.Int.Polynomial.HilbertSyzygy
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Instance.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part2
/-!
# Finite multigraded free resolutions over polynomial rings

Existence of a finite multigraded free resolution with finite homogeneous
basis types for every finitely generated module carrying the campaign
multigrading over `MvPolynomial (Fin n) K`.

Direct source for the existence claim: Hoffman–Wang,
*Regularity and Resolutions for Multigraded Modules*,
https://export.arxiv.org/e-print/math/0601101v1 lines 592-612, which states
that any finitely generated multigraded module has a finite free graded
resolution by finite direct sums of shifted copies of the polynomial algebra.

Motivation and multigraded Betti / Poincaré-series context: Braun–Davis,
*Antichain Simplices*, Journal of Integer Sequences 23 (2020),
https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex lines 856-876,
which records the Hilbert Syzygy consequence that the Poincaré series is a
polynomial over a polynomial ring. That JIS passage motivates this edge but
is not its proof source.

This edge claims finite termination only: no numerical bound `≤ n`, no
minimality or uniqueness, no base change, and no Poincaré-series conclusion.
-/


namespace MetaMathlibExt

universe u

open CategoryTheory MvPolynomial

noncomputable section

section mgsyz_FreeDecomposition

variable (K : Type u) [Field K] {n : ℕ} {ι : Type u}

variable (δ : ι → Fin n →₀ ℤ)

theorem mgsyz_decompose_free_apply (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) :
    (((DirectSum.decompose (mgsyz_freeComponent K δ) f) β :
      mgsyz_freeComponent K δ β) : ι →₀ MvPolynomial (Fin n) K) =
      mgsyz_freeProj K δ β f := by
  conv_lhs => rw [mgsyz_sum_freeProj K δ f]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply]
  by_cases hβ : β ∈ mgsyz_freeDegrees K δ f
  · rw [Finset.sum_eq_single β]
    · exact DirectSum.decompose_of_mem_same _ (mgsyz_freeProj_mem K δ β f)
    · intro γ hγ hγβ
      apply Subtype.ext
      exact DirectSum.decompose_of_mem_ne _ (mgsyz_freeProj_mem K δ γ f) hγβ
    · intro h
      exact (h hβ).elim
  · rw [Finset.sum_eq_zero]
    · ext j a
      by_cases ha : (f j).coeff a = 0
      · simp [mgsyz_freeProj_apply, MvPolynomial.coeff_monomial, ha]
      · have haj : a ∈ (f j).support := MvPolynomial.mem_support_iff.mpr ha
        have hj : j ∈ f.support := by
          rw [Finsupp.mem_support_iff]
          intro hfj
          rw [hfj] at ha
          simp at ha
        have hdeg : natDegreeToInt a + δ j ≠ β := by
          intro h
          apply hβ
          rw [mgsyz_freeDegrees, Finset.mem_biUnion]
          exact ⟨j, hj, Finset.mem_image.mpr ⟨a, haj, h⟩⟩
        simp [mgsyz_freeProj_apply, MvPolynomial.coeff_monomial, hdeg]
    · intro γ hγ
      apply Subtype.ext
      apply DirectSum.decompose_of_mem_ne _ (mgsyz_freeProj_mem K δ γ f)
      intro hγβ
      subst γ
      exact hβ hγ

end mgsyz_FreeDecomposition
end
end MetaMathlibExt
