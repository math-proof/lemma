/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part6
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def leviFactorAction
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    (L ⧸ I) →ₗ⁅K⁆ Module.End K M := by
  let f := LieModule.toEnd K L M
  have hker : I.toSubmodule ≤ LinearMap.ker (f : L →ₗ[K] Module.End K M) := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext m
    exact hI x hx m
  exact
    { I.toSubmodule.liftQ (f : L →ₗ[K] Module.End K M) hker with
      map_lie' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            rw [← LieSubmodule.Quotient.mk_bracket]
            change f ⁅x, y⁆ = ⁅f x, f y⁆
            exact f.map_lie x y }

@[instance_reducible] noncomputable def leviFactorLieRingModule
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, ⁅x, m⁆ = 0) :
    LieRingModule (L ⧸ I) M :=
  LieRingModule.compLieHom M (leviFactorAction I hI)

end LeviDecomposition
