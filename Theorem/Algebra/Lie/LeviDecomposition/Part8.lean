/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part7
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem levi_factor_exists_isCompl
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] (I : LieIdeal K L)
    [LieAlgebra.IsSemisimple K (L ⧸ I)]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M]
    (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) (W : LieSubmodule K L M) :
    ∃ U : LieSubmodule K L M, IsCompl W U := by
  let _ := leviFactorLieRingModule I hI
  let _ := leviFactorLieModule I hI
  obtain ⟨U, hU⟩ :=
    LieModule.exists_isCompl_of_isSemisimple (leviFactorSubmodule I hI W)
  refine ⟨leviUnfactorSubmodule I hI U, ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule] at hU ⊢
  exact hU

end LeviDecomposition
