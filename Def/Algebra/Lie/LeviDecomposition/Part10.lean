module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theorem.Algebra.Lie.LeviDecomposition.Part10


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

def leviComapMapKerToKer
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L') (J : LieIdeal K L') :
    (leviComapMap f J).ker →ₗ⁅K⁆ f.ker where
  toFun x := ⟨x.1.1, by
    rw [LieHom.mem_ker]
    have hx : leviComapMap f J x.1 = 0 := LieHom.mem_ker.mp x.2
    have h := congrArg Subtype.val hx
    exact h⟩
  map_add' x y := Subtype.ext rfl
  map_smul' c x := Subtype.ext rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl

end LeviDecomposition
