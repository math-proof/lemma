/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part7
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def leviFactorSubmodule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0)
    (W : LieSubmodule K L M) :
    letI := leviFactorLieRingModule I hI
    LieSubmodule K (L ⧸ I) M := by
  letI := leviFactorLieRingModule I hI
  exact
    { W.toSubmodule with
      lie_mem := by
        intro x m hm
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change leviFactorAction I hI (LieSubmodule.Quotient.mk x) m ∈ W
          rw [leviFactorAction_mk I hI]
          exact W.lie_mem hm }

noncomputable def leviUnfactorSubmodule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    letI := leviFactorLieRingModule I hI
    LieSubmodule K (L ⧸ I) M → LieSubmodule K L M := by
  letI := leviFactorLieRingModule I hI
  intro W
  exact
    { W.toSubmodule with
      lie_mem := by
        intro x m hm
        rw [← leviFactorAction_mk I hI]
        exact W.lie_mem hm }

end LeviDecomposition
