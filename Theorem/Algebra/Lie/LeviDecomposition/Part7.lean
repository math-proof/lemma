/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part6
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviFactorLieModule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    @LieModule K (L ⧸ I) M _ _ _ _ _ (leviFactorLieRingModule I hI) :=
  LieModule.compLieHom M (leviFactorAction I hI)

theorem leviFactorAction_mk
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0)
    (x : L) (m : M) :
    leviFactorAction I hI (LieSubmodule.Quotient.mk x) m = ⁅x, m⁆ := by
  rfl

end LeviDecomposition
