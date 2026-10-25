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
import Theorem.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part15
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

noncomputable def mgsyz_next (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : mgsyz_Stage K n := by
  letI : Module K
      (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  exact
    { W := mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K
      addCommGroup := inferInstance
      moduleR := inferInstance
      moduleK := Module.compHom _
        (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
      gW := mgsyz_freeGraded K (mgsyz_delta (K := K) n S)
      N := LinearMap.ker (mgsyz_phi (K := K) n S)
      graded := by
        intro x hx β
        exact @mgsyz_ker_graded K _ n _ _ _ _
          (Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) _ _ _
          (mgsyz_freeGraded K (mgsyz_delta (K := K) n S)) S.gW
          (mgsyz_phi (K := K) n S) (mgsyz_phi_degreeZero K n S) x hx β
      fg := IsNoetherian.noetherian _ }

noncomputable def mgsyz_stage0 (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] : mgsyz_Stage K n where
  W := M
  addCommGroup := inferInstance
  moduleR := inferInstance
  moduleK := inferInstance
  gW := targetGraded
  N := ⊤
  graded := by
    intro x hx β
    exact Submodule.mem_top
  fg := Module.Finite.fg_top

noncomputable def mgsyz_stage (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] : ℕ → mgsyz_Stage K n
  | 0 => mgsyz_stage0 K n M targetGraded
  | k + 1 => mgsyz_next K n (mgsyz_stage K n M targetGraded k)

end mgsyz_Stages
end
end MetaMathlibExt
