/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part9
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviComapMap_surjective
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) (J : LieIdeal K L') :
    Function.Surjective (leviComapMap f J) := by
  intro y
  obtain ⟨x, hx⟩ := hf y
  have hxJ : x ∈ J.comap f := by
    change f x ∈ J
    rw [hx]
    exact y.2
  refine ⟨⟨x, hxJ⟩, ?_⟩
  apply Subtype.ext
  exact hx

end LeviDecomposition
