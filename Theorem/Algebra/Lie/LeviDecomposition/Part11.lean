/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part10
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviComapMapKerToKer_injective
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (J : LieIdeal K L') :
    Function.Injective (leviComapMapKerToKer f J) := by
  intro x y h
  have hxy := congrArg (fun z : f.ker ↦ z.1) h
  change x.1.1 = y.1.1 at hxy
  exact Subtype.ext (Subtype.ext hxy)

theorem levi_isSolvable_comap
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) [LieAlgebra.IsSolvable f.ker]
    (J : LieIdeal K L') [LieAlgebra.IsSolvable J] :
    LieAlgebra.IsSolvable (J.comap f) := by
  let q := leviComapMap f J
  have _ : LieAlgebra.IsSolvable q.ker :=
    (leviComapMapKerToKer_injective f J).lieAlgebra_isSolvable
  exact levi_isSolvable_of_ker_quotient q (leviComapMap_surjective f hf J)

end LeviDecomposition
