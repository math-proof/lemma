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
import Def.Algebra.Lie.Ado.Part3
attribute [local instance 100] LieRing.ofAssociativeRing

/-!
# Ado's theorem

This file proves Ado's theorem over fields of characteristic zero. It builds finite-dimensional
representations from quotients of universal enveloping algebras, then uses the Levi decomposition.
-/


namespace MathlibExt.Algebra.Lie.LandmarkWanted

theorem ado_derivation_ext
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (d e : UniversalEnvelopingAlgebra K L →ₗ[K] UniversalEnvelopingAlgebra K L)
    (hd : ∀ u v, d (u * v) = u * d v + d u * v)
    (he : ∀ u v, e (u * v) = u * e v + e u * v)
    (hι : ∀ x, d (UniversalEnvelopingAlgebra.ι K x) =
      e (UniversalEnvelopingAlgebra.ι K x)) : d = e := by
  let fd := adoDerivationToSquareZero d hd
  let fe := adoDerivationToSquareZero e he
  have hfe : fd = fe := by
    apply UniversalEnvelopingAlgebra.hom_ext K
    ext x
    · rfl
    · exact hι x
  apply LinearMap.ext
  intro u
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hfe u)

theorem adoExtendDerivation_add
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D E : LieDerivation K L L) :
    adoExtendDerivation (D + E) = adoExtendDerivation D + adoExtendDerivation E := by
  apply ado_derivation_ext
  · exact adoExtendDerivation_mul (D + E)
  · intro u v
    simp only [LinearMap.add_apply, adoExtendDerivation_mul]
    noncomm_ring
  · intro x
    change adoExtendDerivation (D + E) (UniversalEnvelopingAlgebra.ι K x) =
      adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x) +
        adoExtendDerivation E (UniversalEnvelopingAlgebra.ι K x)
    rw [adoExtendDerivation_ι, adoExtendDerivation_ι, adoExtendDerivation_ι]
    simp

theorem adoExtendDerivation_smul
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (c : K) (D : LieDerivation K L L) :
    adoExtendDerivation (c • D) = c • adoExtendDerivation D := by
  apply ado_derivation_ext
  · exact adoExtendDerivation_mul (c • D)
  · intro u v
    simp only [LinearMap.smul_apply, adoExtendDerivation_mul, smul_add,
      mul_smul_comm, smul_mul_assoc]
  · intro x
    change adoExtendDerivation (c • D) (UniversalEnvelopingAlgebra.ι K x) =
      c • adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x)
    rw [adoExtendDerivation_ι, adoExtendDerivation_ι]
    simp

theorem adoExtendDerivation_lie
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D E : LieDerivation K L L) :
    adoExtendDerivation ⁅D, E⁆ = ⁅adoExtendDerivation D, adoExtendDerivation E⁆ := by
  apply ado_derivation_ext
  · exact adoExtendDerivation_mul ⁅D, E⁆
  · intro u v
    change adoExtendDerivation D (adoExtendDerivation E (u * v)) -
        adoExtendDerivation E (adoExtendDerivation D (u * v)) =
      u * (adoExtendDerivation D (adoExtendDerivation E v) -
        adoExtendDerivation E (adoExtendDerivation D v)) +
      (adoExtendDerivation D (adoExtendDerivation E u) -
        adoExtendDerivation E (adoExtendDerivation D u)) * v
    simp only [adoExtendDerivation_mul, map_add]
    noncomm_ring
  · intro x
    change adoExtendDerivation ⁅D, E⁆ (UniversalEnvelopingAlgebra.ι K x) =
      adoExtendDerivation D
          (adoExtendDerivation E (UniversalEnvelopingAlgebra.ι K x)) -
        adoExtendDerivation E
          (adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x))
    rw [adoExtendDerivation_ι, adoExtendDerivation_ι, adoExtendDerivation_ι,
      adoExtendDerivation_ι, adoExtendDerivation_ι, LieDerivation.lie_apply, map_sub]

end MathlibExt.Algebra.Lie.LandmarkWanted
