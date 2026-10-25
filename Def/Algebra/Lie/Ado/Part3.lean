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
import Theorem.Algebra.Lie.Ado.Part2
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
