module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theorem.Algebra.Lie.LeviDecomposition.Part14


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

def leviSubalgebraComapMap
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    T.comap q →ₗ⁅K⁆ T where
  toFun x := ⟨q x.1, x.2⟩
  map_add' x y := Subtype.ext (q.map_add x.1 y.1)
  map_smul' a x := Subtype.ext (q.map_smul a x.1)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact q.map_lie x.1 y.1

end LeviDecomposition
