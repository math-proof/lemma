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

theorem mgsyz_natDegreeToInt_add {n : ℕ} (a b : Fin n →₀ ℕ) :
    natDegreeToInt (a + b) = natDegreeToInt a + natDegreeToInt b := by
  apply Finsupp.mapRange_add
  exact Nat.cast_add

theorem mgsyz_natDegreeToInt_zero {n : ℕ} :
    natDegreeToInt (0 : Fin n →₀ ℕ) = 0 := by
  exact Finsupp.mapRange_zero

theorem mgsyz_natDegreeToInt_eq_zero_iff {n : ℕ} (a : Fin n →₀ ℕ) :
    natDegreeToInt a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply Finsupp.mapRange_injective (fun x : ℕ => (x : ℤ)) (by simp)
        Nat.cast_injective
    simpa [natDegreeToInt] using h
  · rintro rfl
    exact mgsyz_natDegreeToInt_zero

end
end MetaMathlibExt
