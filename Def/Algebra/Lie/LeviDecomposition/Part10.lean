/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part10
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
