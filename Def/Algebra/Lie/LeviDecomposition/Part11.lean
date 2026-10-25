/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part11
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

def leviMapRestrict
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (I : LieIdeal K L) :
    I →ₗ⁅K⁆ I.map f where
  toFun x := ⟨f x.1, LieIdeal.mem_map x.2⟩
  map_add' x y := Subtype.ext (f.map_add x.1 y.1)
  map_smul' c x := Subtype.ext (f.map_smul c x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact f.map_lie x.1 y.1

end LeviDecomposition
