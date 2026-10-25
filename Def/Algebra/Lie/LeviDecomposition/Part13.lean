/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part13
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

def leviStabilizer
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) :
    LieSubalgebra K L where
  carrier := {x | ⁅x, f⁆ = 0}
  zero_mem' := by
    change ⁅0, f⁆ = 0
    rw [zero_lie]
  add_mem' {x y} hx hy := by
    change ⁅x + y, f⁆ = 0
    rw [add_lie, hx, hy, add_zero]
  smul_mem' a x hx := by
    change ⁅a • x, f⁆ = 0
    rw [smul_lie, hx, smul_zero]
  lie_mem' := by
    intro x y hx hy
    change ⁅⁅x, y⁆, f⁆ = 0
    rw [lie_lie, hx, hy]
    simp

end LeviDecomposition
