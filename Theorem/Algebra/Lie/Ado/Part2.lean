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
public import Def.Algebra.Lie.Ado.Part2


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

theorem adoExtendDerivation_ι
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) (x : L) :
    adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x) =
      UniversalEnvelopingAlgebra.ι K (D x) := by
  change (adoUniversalLift D (UniversalEnvelopingAlgebra.ι K x)).snd = _
  rw [adoUniversalLift, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

theorem adoExtendDerivation_mul
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) (u v : UniversalEnvelopingAlgebra K L) :
    adoExtendDerivation D (u * v) =
      u * adoExtendDerivation D v + adoExtendDerivation D u * v := by
  change (adoUniversalLift D (u * v)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul, adoUniversalLift_fst,
    adoUniversalLift_fst]
  rfl

end MathlibExt.Algebra.Lie.LandmarkWanted
