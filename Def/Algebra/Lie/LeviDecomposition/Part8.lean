module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theorem.Algebra.Lie.LeviDecomposition.Part8


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/
namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

def leviQuotientMk
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : L →ₗ⁅K⁆ L ⧸ I :=
  { (LieSubmodule.Quotient.mk' I : L →ₗ[K] L ⧸ I) with
    map_lie' := by
      intro x y
      change LieSubmodule.Quotient.mk ⁅x, y⁆ =
        ⁅LieSubmodule.Quotient.mk x, LieSubmodule.Quotient.mk y⁆
      exact LieSubmodule.Quotient.mk_bracket I x y }

end LeviDecomposition
