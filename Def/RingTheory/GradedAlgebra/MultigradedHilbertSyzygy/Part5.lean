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
import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part5
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

noncomputable def mgsyz_freeGraded :
    MultigradedPolynomialModule K n (ι →₀ MvPolynomial (Fin n) K) where
  component := mgsyz_freeComponent K δ
  decomposition := mgsyz_freeDecomposition K δ
  smul_via_C := by
    intro k f
    rfl
  monomial_mem := by
    intro s c α f hf j m hm
    change m ∈ (MvPolynomial.monomial s c * f j).support at hm
    have hmcoeff := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_monomial_mul'] at hmcoeff
    split at hmcoeff
    next hs =>
      have hrest : m - s ∈ (f j).support := by
        rw [MvPolynomial.mem_support_iff]
        intro hzero
        simp [hzero] at hmcoeff
      have hdeg := hf j (m - s) hrest
      have hms : m - s + s = m := tsub_add_cancel_of_le hs
      have hnat : natDegreeToInt m =
          natDegreeToInt (m - s) + natDegreeToInt s := by
        conv_lhs => rw [← hms, mgsyz_natDegreeToInt_add]
      calc
        natDegreeToInt m + δ j =
            (natDegreeToInt (m - s) + δ j) + natDegreeToInt s := by
          rw [hnat]
          abel
        _ = α + natDegreeToInt s := by rw [hdeg]
    next hs =>
      simp at hmcoeff

end mgsyz_FreeDecomposition
end
end MetaMathlibExt
