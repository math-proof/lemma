module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Engel
public import Mathlib.Algebra.Lie.LieTheorem
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.SemiDirect
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Set.Finite.List
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Def.Algebra.Lie.LeviDecomposition.Part15
public import Theorem.Fin.EqSum_SMul.of.Basis


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

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
