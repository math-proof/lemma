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
public import Theorem.Algebra.Lie.Ado.Part2


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

def adoDerivationToSquareZero
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (d : A →ₗ[K] A) (hd : ∀ u v, d (u * v) = u * d v + d u * v) :
    A →ₐ[K] TrivSqZeroExt A A := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [one_mul, mul_one] at h
    have h' := congrArg (fun z => z - d 1) h
    simpa using h'.symm
  exact
    { toFun := fun u => (u, d u)
      map_one' := by
        apply TrivSqZeroExt.ext
        · rfl
        · exact hd1
      map_mul' := by
        intro u v
        apply TrivSqZeroExt.ext
        · rfl
        · exact hd u v
      map_zero' := by
        apply TrivSqZeroExt.ext <;> simp
      map_add' := by
        intro u v
        apply TrivSqZeroExt.ext
        · rfl
        · exact d.map_add u v
      commutes' := by
        intro c
        rw [TrivSqZeroExt.algebraMap_eq_inl']
        apply TrivSqZeroExt.ext
        · rfl
        · simpa [Algebra.smul_def, hd1] using d.map_smul c 1 }

end MathlibExt.Algebra.Lie.LandmarkWanted
