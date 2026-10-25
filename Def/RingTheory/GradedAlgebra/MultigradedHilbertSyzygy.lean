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
import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy
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

def mgsyz_freeComponent (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (α : Fin n →₀ ℤ) :
    letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    Submodule K (ι →₀ MvPolynomial (Fin n) K) := by
  letI : Module K (ι →₀ MvPolynomial (Fin n) K) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  exact
    { carrier := fun f => ∀ j a, a ∈ (f j).support →
        natDegreeToInt a + δ j = α
      zero_mem' := by
        intro j a ha
        simp at ha
      add_mem' := by
        intro f g hf hg j a ha
        have ha' := MvPolynomial.support_add ha
        simp only [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · exact hf j a ha'
        · exact hg j a ha'
      smul_mem' := by
        intro k f hf j a ha
        change a ∈ (MvPolynomial.C k * f j).support at ha
        rw [MvPolynomial.C_mul'] at ha
        exact hf j a (MvPolynomial.support_smul ha) }

noncomputable def mgsyz_freeProj (K : Type u) [Field K] {n : ℕ} {ι : Type u}
    (δ : ι → Fin n →₀ ℤ) (β : Fin n →₀ ℤ)
    (f : ι →₀ MvPolynomial (Fin n) K) : ι →₀ MvPolynomial (Fin n) K := by
  classical
  exact ∑ j ∈ f.support, Finsupp.single j
    (∑ a ∈ (f j).support with natDegreeToInt a + δ j = β,
      MvPolynomial.monomial a ((f j).coeff a))

end
end MetaMathlibExt
