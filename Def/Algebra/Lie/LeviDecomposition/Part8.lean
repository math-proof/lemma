/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part8
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
