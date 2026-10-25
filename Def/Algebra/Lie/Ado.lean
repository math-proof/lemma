/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Def.Algebra.Lie.LeviDecomposition.Part15
import Lemma.Fin.EqSum_SMul.of.Basis
attribute [local instance 100] LieRing.ofAssociativeRing

/-!
# Ado's theorem

This file proves Ado's theorem over fields of characteristic zero. It builds finite-dimensional
representations from quotients of universal enveloping algebras, then uses the Levi decomposition.
-/


namespace MathlibExt.Algebra.Lie.LandmarkWanted

def adoDirectSum
    {K L V W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W) :
    L →ₗ⁅K⁆ Module.End K (V × W) :=
  (LinearMap.prodMapAlgHom K V W).toLieHom.comp (ρ.prod σ)

def adoAbelianShearLinear
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] :
    L →ₗ[K] Module.End K (L × K) where
  toFun x :=
    { toFun := fun p => (p.2 • x, 0)
      map_add' := by
        intro p q
        ext <;> simp [add_smul]
      map_smul' := by
        intro c p
        ext <;> simp [mul_smul] }
  map_add' x y := by
    ext p <;> simp [smul_add]
  map_smul' c x := by
    ext p <;> simp [smul_smul, mul_comm]

def adoAbelianShear
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsLieAbelian L] :
    L →ₗ⁅K⁆ Module.End K (L × K) where
  toLinearMap := adoAbelianShearLinear
  map_lie' := by
    intro x y
    rw [trivial_lie_zero L L]
    ext p <;> simp [adoAbelianShearLinear, Module.End.lie_apply]

def adoLieDerivationToSquareZero
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) :
    L →ₗ⁅K⁆ TrivSqZeroExt (UniversalEnvelopingAlgebra K L)
      (UniversalEnvelopingAlgebra K L) where
  toLinearMap := (UniversalEnvelopingAlgebra.ι K).toLinearMap.prod
    ((UniversalEnvelopingAlgebra.ι K).toLinearMap.comp D.toLinearMap)
  map_lie' := by
    intro x y
    apply TrivSqZeroExt.ext
    · exact LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) x y
    · change UniversalEnvelopingAlgebra.ι K (D ⁅x, y⁆) =
        (UniversalEnvelopingAlgebra.ι K x * UniversalEnvelopingAlgebra.ι K (D y) +
          UniversalEnvelopingAlgebra.ι K (D x) * UniversalEnvelopingAlgebra.ι K y) -
        (UniversalEnvelopingAlgebra.ι K y * UniversalEnvelopingAlgebra.ι K (D x) +
          UniversalEnvelopingAlgebra.ι K (D y) * UniversalEnvelopingAlgebra.ι K x)
      rw [D.apply_lie_eq_add, map_add, LieHom.map_lie, LieHom.map_lie]
      simp only [Ring.lie_def]
      noncomm_ring

def adoUniversalLift
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) :
    UniversalEnvelopingAlgebra K L →ₐ[K]
      TrivSqZeroExt (UniversalEnvelopingAlgebra K L)
        (UniversalEnvelopingAlgebra K L) :=
  UniversalEnvelopingAlgebra.lift K (adoLieDerivationToSquareZero D)

end MathlibExt.Algebra.Lie.LandmarkWanted
