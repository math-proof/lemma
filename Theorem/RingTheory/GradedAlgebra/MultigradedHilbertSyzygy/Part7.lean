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
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part6
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

theorem mgsyz_linearCombination_isDegreeZero
    {W : Type u} [AddCommGroup W] [Module (MvPolynomial (Fin n) K) W] [Module K W]
    (gW : MultigradedPolynomialModule K n W) (g : ι → W)
    (hg : ∀ j, g j ∈ gW.component (δ j)) :
    IsDegreeZero (mgsyz_freeGraded K δ) gW
      (Finsupp.linearCombination (MvPolynomial (Fin n) K) g) := by
  classical
  intro α f hf
  change f ∈ mgsyz_freeComponent K δ α at hf
  rw [Finsupp.linearCombination_apply]
  change (∑ j ∈ f.support, f j • g j) ∈ gW.component α
  apply Submodule.sum_mem
  intro j hj
  rw [MvPolynomial.as_sum (f j), Finset.sum_smul]
  apply Submodule.sum_mem
  intro a ha
  have hmon := gW.monomial_mem a ((f j).coeff a) (δ j) (g j) (hg j)
  rw [add_comm, hf j a ha] at hmon
  exact hmon

end mgsyz_FreeDecomposition
end
end MetaMathlibExt
