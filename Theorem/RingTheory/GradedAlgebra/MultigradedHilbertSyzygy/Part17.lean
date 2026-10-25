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
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part15
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

theorem mgsyz_d_apply (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ)
    (x : mgsyz_Fk K n M targetGraded (k + 1)) :
    mgsyz_d K n M targetGraded k x =
      mgsyz_phi (K := K) n (mgsyz_stage K n M targetGraded (k + 1)) x :=
  rfl

theorem mgsyz_d_comp_succ (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    (mgsyz_d K n M targetGraded k).comp
      (mgsyz_d K n M targetGraded (k + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (mgsyz_phik_comp_succ K n M targetGraded k) x

theorem mgsyz_d_range_eq_ker (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    LinearMap.range (mgsyz_d K n M targetGraded (k + 1)) =
      LinearMap.ker (mgsyz_d K n M targetGraded k) := by
  change LinearMap.range (mgsyz_phik K n M targetGraded (k + 2)) =
    LinearMap.ker (mgsyz_phik K n M targetGraded (k + 1))
  exact mgsyz_phik_range_eq_ker K n M targetGraded (k + 1)

end mgsyz_Stages
end
end MetaMathlibExt
