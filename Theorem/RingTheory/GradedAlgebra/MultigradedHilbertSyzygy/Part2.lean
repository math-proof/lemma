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
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
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

theorem mgsyz_freeProj_apply (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) (j : ι) :
    mgsyz_freeProj K δ β f j =
      ∑ a ∈ (f j).support with natDegreeToInt a + δ j = β,
        MvPolynomial.monomial a ((f j).coeff a) := by
  classical
  rw [mgsyz_freeProj, Finsupp.finsetSum_apply]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · intro h
      exact (h hj).elim
  · rw [Finset.sum_eq_zero]
    · have hfj : f j = 0 := by
        simpa [Finsupp.mem_support_iff] using hj
      rw [hfj]
      simp
    · intro b hb
      simp [show b ≠ j by
        intro h
        exact hj (h ▸ hb)]

theorem mgsyz_freeProj_mem (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) :
    letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    mgsyz_freeProj K δ β f ∈ mgsyz_freeComponent K δ β := by
  intro j a ha
  rw [mgsyz_freeProj_apply] at ha
  by_contra hdeg
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, hdeg] at ha

end
end MetaMathlibExt
