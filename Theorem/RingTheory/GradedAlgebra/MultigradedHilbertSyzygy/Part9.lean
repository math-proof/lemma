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
import Instance.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part4
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

attribute [local instance] mgsyz_Stage.addCommGroup mgsyz_Stage.moduleR
  mgsyz_Stage.moduleK

section mgsyz_HomogeneousSpan

variable (K : Type u) [Field K] (n : ℕ) {W : Type u}
  [AddCommGroup W] [Module (MvPolynomial (Fin n) K) W] [Module K W]

variable (gW : MultigradedPolynomialModule K n W)

theorem mgsyz_exists_homogeneous_span
    (N : Submodule (MvPolynomial (Fin n) K) W)
    (graded : ∀ x ∈ N, ∀ β,
      (((DirectSum.decompose gW.component x) β : gW.component β) : W) ∈ N)
    (fg : N.FG) :
    ∃ s : Finset W,
      (∀ m ∈ s, ∃ α : Fin n →₀ ℤ, m ∈ gW.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K) (s : Set W) = N := by
  classical
  obtain ⟨genCount, genFun, genSpan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp fg
  let s : Finset W := Finset.univ.biUnion fun genIdx =>
    (DirectSum.decompose gW.component (genFun genIdx)).support.image
      (fun deg => (((DirectSum.decompose gW.component (genFun genIdx)) deg) : W))
  refine ⟨s, ?_, le_antisymm ?_ ?_⟩
  · intro homElem homMem
    rw [Finset.mem_biUnion] at homMem
    obtain ⟨genIdx, _, imageMem⟩ := homMem
    rw [Finset.mem_image] at imageMem
    obtain ⟨deg, _, rfl⟩ := imageMem
    exact ⟨deg, ((DirectSum.decompose gW.component (genFun genIdx)) deg).property⟩
  · apply Submodule.span_le.mpr
    intro homElem homMem
    rw [Finset.mem_coe, Finset.mem_biUnion] at homMem
    obtain ⟨genIdx, _, imageMem⟩ := homMem
    rw [Finset.mem_image] at imageMem
    obtain ⟨deg, _, rfl⟩ := imageMem
    apply graded (genFun genIdx)
    rw [← genSpan]
    exact Submodule.subset_span (Set.mem_range_self genIdx)
  · rw [← genSpan]
    apply Submodule.span_le.mpr
    intro genElem genRangeMem
    obtain ⟨genIdx, rfl⟩ := genRangeMem
    have recon : genFun genIdx =
        ∑ deg ∈ (DirectSum.decompose gW.component (genFun genIdx)).support,
          (((DirectSum.decompose gW.component (genFun genIdx)) deg) : W) :=
      (DirectSum.sum_support_decompose gW.component (genFun genIdx)).symm
    rw [recon]
    apply Submodule.sum_mem
    intro deg degMem
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨genIdx, Finset.mem_univ genIdx,
      Finset.mem_image.mpr ⟨deg, degMem, rfl⟩⟩

end mgsyz_HomogeneousSpan
end
end MetaMathlibExt
