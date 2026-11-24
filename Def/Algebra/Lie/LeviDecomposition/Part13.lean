module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theorem.Algebra.Lie.LeviDecomposition.Part13


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
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
