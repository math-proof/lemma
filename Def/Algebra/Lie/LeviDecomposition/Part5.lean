/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part5
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def leviHomScalar
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
    leviHomScalarMaps W →ₗ[K] K where
  toFun f := Classical.choose f.2
  map_add' f g := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (f + g).property • w = (f + g : M →ₗ[K] W) w :=
        (Classical.choose_spec (f + g).property w).symm
      _ = f.1 w + g.1 w := rfl
      _ = Classical.choose f.property • w + Classical.choose g.property • w := by
        rw [Classical.choose_spec f.property w, Classical.choose_spec g.property w]
      _ = (Classical.choose f.property + Classical.choose g.property) • w :=
        (add_smul _ _ _).symm
  map_smul' c f := by
    apply levi_scalar_unique W hW
    intro w
    calc
      Classical.choose (c • f).property • w = (c • f : M →ₗ[K] W) w :=
        (Classical.choose_spec (c • f).property w).symm
      _ = c • f.1 w := rfl
      _ = c • (Classical.choose f.property • w) := by
        rw [Classical.choose_spec f.property w]
      _ = (c * Classical.choose f.property) • w := (mul_smul _ _ _).symm

end LeviDecomposition
