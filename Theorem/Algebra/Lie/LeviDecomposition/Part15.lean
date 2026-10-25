/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part14
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviSubalgebraComapMap_surjective
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G)
    (hq : Function.Surjective q) (T : LieSubalgebra K G) :
    Function.Surjective (leviSubalgebraComapMap q T) := by
  intro y
  obtain ⟨x, hx⟩ := hq y
  have hxT : x ∈ T.comap q := by
    change q x ∈ T
    rw [hx]
    exact y.2
  refine ⟨⟨x, hxT⟩, ?_⟩
  apply Subtype.ext
  exact hx

end LeviDecomposition
