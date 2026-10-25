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
import Theorem.Algebra.Lie.Ado.Part3
attribute [local instance 100] LieRing.ofAssociativeRing

/-!
# Ado's theorem

This file proves Ado's theorem over fields of characteristic zero. It builds finite-dimensional
representations from quotients of universal enveloping algebras, then uses the Levi decomposition.
-/


namespace MathlibExt.Algebra.Lie.LandmarkWanted

def adoExtendDerivationHom
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] :
    LieDerivation K L L →ₗ⁅K⁆
      Module.End K (UniversalEnvelopingAlgebra K L) where
  toLinearMap :=
    { toFun := adoExtendDerivation
      map_add' := adoExtendDerivation_add
      map_smul' := adoExtendDerivation_smul }
  map_lie' := fun {D E} => adoExtendDerivation_lie D E

def adoIdealAd
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : L →ₗ⁅K⁆ LieDerivation K I I where
  toLinearMap :=
    { toFun := fun x =>
        { toLinearMap := LieModule.toEnd K L I x
          leibniz' := by
            intro y z
            apply Subtype.ext
            change ⁅x, ⁅y.1, z.1⁆⁆ = ⁅y.1, ⁅x, z.1⁆⁆ - ⁅z.1, ⁅x, y.1⁆⁆
            rw [sub_eq_add_neg, ← lie_skew z.1 ⁅x, y.1⁆, lie_lie x y.1 z.1]
            abel }
      map_add' := by
        intro x y
        ext z
        simp
      map_smul' := by
        intro c x
        ext z
        simp }
  map_lie' := by
    intro x y
    ext z
    exact lie_lie x y z.1

def adoLeftRegularLie
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] :
    L →ₗ⁅K⁆ Module.End K (UniversalEnvelopingAlgebra K L) :=
  (Algebra.lmul K (UniversalEnvelopingAlgebra K L)).toLieHom.comp
    (UniversalEnvelopingAlgebra.ι K)

def adoSemidirectRepresentation
    {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
    [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I) :
    (I ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (UniversalEnvelopingAlgebra K I) where
  toLinearMap :=
    (adoLeftRegularLie (K := K) (L := I)).toLinearMap.comp
        (LieAlgebra.SemiDirectSum.projl ψ) +
      ((adoExtendDerivationHom (K := K) (L := I)).comp ψ).toLinearMap.comp
        (LieAlgebra.SemiDirectSum.projr ψ).toLinearMap
  map_lie' := by
    intro x y
    ext u
    change
      UniversalEnvelopingAlgebra.ι K
            (⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left) * u +
          adoExtendDerivation (ψ ⁅x.right, y.right⁆) u =
        (UniversalEnvelopingAlgebra.ι K x.left *
              (UniversalEnvelopingAlgebra.ι K y.left * u +
                adoExtendDerivation (ψ y.right) u) +
            adoExtendDerivation (ψ x.right)
              (UniversalEnvelopingAlgebra.ι K y.left * u +
                adoExtendDerivation (ψ y.right) u)) -
          (UniversalEnvelopingAlgebra.ι K y.left *
              (UniversalEnvelopingAlgebra.ι K x.left * u +
                adoExtendDerivation (ψ x.right) u) +
            adoExtendDerivation (ψ y.right)
              (UniversalEnvelopingAlgebra.ι K x.left * u +
                adoExtendDerivation (ψ x.right) u))
    rw [LieHom.map_lie ψ]
    have hlie := LinearMap.congr_fun
      (adoExtendDerivation_lie (ψ x.right) (ψ y.right)) u
    change adoExtendDerivation ⁅ψ x.right, ψ y.right⁆ u =
      adoExtendDerivation (ψ x.right) (adoExtendDerivation (ψ y.right) u) -
        adoExtendDerivation (ψ y.right) (adoExtendDerivation (ψ x.right) u) at hlie
    rw [hlie]
    simp only [map_add, map_sub, LieHom.map_lie, adoExtendDerivation_mul,
      adoExtendDerivation_ι, Ring.lie_def]
    noncomm_ring

end MathlibExt.Algebra.Lie.LandmarkWanted
