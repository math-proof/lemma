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
import Instance.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part3
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

section mgsyz_KernelGrading

variable {K : Type u} [Field K] {n : ℕ}

variable {F W : Type u} [AddCommGroup F] [Module (MvPolynomial (Fin n) K) F]
  [Module K F] [AddCommGroup W] [Module (MvPolynomial (Fin n) K) W] [Module K W]

variable (gF : MultigradedPolynomialModule K n F)
  (gW : MultigradedPolynomialModule K n W)

theorem mgsyz_ker_graded
    (φ : F →ₗ[MvPolynomial (Fin n) K] W) (hφ : IsDegreeZero gF gW φ)
    (q : F) (hq : q ∈ LinearMap.ker φ) (β : Fin n →₀ ℤ) :
    (((DirectSum.decompose gF.component q) β : gF.component β) : F) ∈
      LinearMap.ker φ := by
  classical
  rw [LinearMap.mem_ker]
  let qβ : F := ((DirectSum.decompose gF.component q) β : gF.component β)
  have hqβmem : qβ ∈ gF.component β :=
    ((DirectSum.decompose gF.component q) β).property
  have hφβmem : φ qβ ∈ gW.component β := hφ β qβ hqβmem
  let s := (DirectSum.decompose gF.component q).support
  have hsumF : (∑ γ ∈ s,
      (((DirectSum.decompose gF.component q) γ : gF.component γ) : F)) = q :=
    DirectSum.sum_support_decompose gF.component q
  have hsumW : (∑ γ ∈ s, φ
      (((DirectSum.decompose gF.component q) γ : gF.component γ) : F)) = 0 := by
    rw [← map_sum, hsumF]
    exact LinearMap.mem_ker.mp hq
  have hdec := congrArg (DirectSum.decompose gW.component) hsumW
  rw [DirectSum.decompose_sum, DirectSum.decompose_zero] at hdec
  have hβeq := congrArg (fun z => ((z β : gW.component β) : W)) hdec
  rw [DFinsupp.finsetSum_apply] at hβeq
  by_cases hβs : β ∈ s
  · have hoff : ∀ γ ∈ s, γ ≠ β →
        (DirectSum.decompose gW.component (φ
          (((DirectSum.decompose gF.component q) γ : gF.component γ) : F))) β = 0 := by
      intro γ hγ hγβ
      apply Subtype.ext
      apply DirectSum.decompose_of_mem_ne gW.component
      · exact hφ γ _ ((DirectSum.decompose gF.component q) γ).property
      · exact hγβ
    have hsingle := Finset.sum_eq_single β hoff (fun h => (h hβs).elim)
    rw [hsingle] at hβeq
    exact (DirectSum.decompose_of_mem_same gW.component hφβmem).symm.trans hβeq
  · have hzero : (DirectSum.decompose gF.component q) β = 0 := by
      by_contra h
      apply hβs
      simpa [s] using DFinsupp.mem_support_iff.mpr h
    change φ qβ = 0
    simp [qβ, hzero]

end mgsyz_KernelGrading
end
end MetaMathlibExt
