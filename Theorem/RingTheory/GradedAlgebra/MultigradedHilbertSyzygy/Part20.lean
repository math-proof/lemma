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
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part18
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

section mgsyz_Stages

set_option backward.isDefEq.respectTransparency false in
theorem mgsyz_zero_short_exact (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    (CategoryTheory.ShortComplex.mk
      ((mgsyz_complex K n M targetGraded).d 1 0)
      (ModuleCat.ofHom (mgsyz_aug K n M targetGraded))
      (mgsyz_complex_d_comp_aug K n M targetGraded)).Exact := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (mgsyz_d K n M targetGraded 0) =
    LinearMap.ker (mgsyz_aug K n M targetGraded)
  exact mgsyz_d_zero_range_eq_aug_ker K n M targetGraded

theorem mgsyz_aug_epi (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    Epi (ModuleCat.ofHom (mgsyz_aug K n M targetGraded)) := by
  rw [ModuleCat.epi_iff_surjective]
  exact mgsyz_aug_surjective K n M targetGraded

set_option backward.isDefEq.respectTransparency false in
theorem mgsyz_complex_exactAt_succ (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    (mgsyz_complex K n M targetGraded).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (mgsyz_complex K n M targetGraded) (k + 2) (k + 1) k (by simp) (by simp)]
  rw [show k + 2 = (k + 1) + 1 by omega]
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    mgsyz_complex, ChainComplex.of_d, ModuleCat.hom_ofHom] using
    mgsyz_d_range_eq_ker K n M targetGraded k

set_option backward.isDefEq.respectTransparency false in
theorem mgsyz_pi_quasiIso (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    QuasiIso (mgsyz_pi K n M targetGraded) := by
  constructor
  intro i
  cases i with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        CategoryTheory.ShortComplex.quasiIso_iff_of_zeros']
      · simp only [mgsyz_pi]
        exact ⟨mgsyz_zero_short_exact K n M targetGraded,
          mgsyz_aug_epi K n M targetGraded⟩
      all_goals rfl
  | succ k =>
      rw [quasiIsoAt_iff_exactAt']
      · exact mgsyz_complex_exactAt_succ K n M targetGraded k
      · exact ChainComplex.exactAt_succ_single_obj _ k

end mgsyz_Stages
end
end MetaMathlibExt
