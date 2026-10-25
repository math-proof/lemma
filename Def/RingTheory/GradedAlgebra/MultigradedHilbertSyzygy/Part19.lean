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
import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part20
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

noncomputable def mgsyz_resolution (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M) where
  complex := mgsyz_complex K n M targetGraded
  projective _i := ModuleCat.projective_of_free Finsupp.basisSingleOne
  π := mgsyz_pi K n M targetGraded
  quasiIso := mgsyz_pi_quasiIso K n M targetGraded

set_option backward.isDefEq.respectTransparency false in
noncomputable def mgsyz_multigradedResolution
    (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    MultigradedFreeResolution K n M targetGraded
      (mgsyz_resolution K n M targetGraded)
      (mgsyz_ιk K n M targetGraded) where
  termFree i := by
    letI : Module K (mgsyz_Fk K n M targetGraded i) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    simpa only [mgsyz_resolution, mgsyz_complex, ChainComplex.of_X] using
      (mgsyz_freeModule K
        (mgsyz_delta (K := K) n (mgsyz_stage K n M targetGraded i)))
  diffDegreeZero i := by
    let : Module K (mgsyz_Fk K n M targetGraded (i + 1)) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    let : Module K (mgsyz_Fk K n M targetGraded i) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    intro α m hm
    simpa only [mgsyz_resolution, mgsyz_complex, ChainComplex.of_d,
      ModuleCat.hom_ofHom, mgsyz_d_apply, mgsyz_stage, mgsyz_next,
      mgsyz_freeModule, id_eq] using
      (mgsyz_phi_degreeZero K n
        (mgsyz_stage K n M targetGraded (i + 1)) α m hm)
  augDegreeZero := by
    let : Module K (mgsyz_Fk K n M targetGraded 0) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
    intro α m hm
    simp only [mgsyz_resolution, mgsyz_pi,
      ChainComplex.toSingle₀Equiv_symm_apply_f_zero, ModuleCat.hom_ofHom]
    change mgsyz_phi (K := K) n
      (mgsyz_stage K n M targetGraded 0) m ∈ targetGraded.component α
    exact mgsyz_phi_degreeZero K n
      (mgsyz_stage K n M targetGraded 0) α m hm

end mgsyz_Stages
end
end MetaMathlibExt
