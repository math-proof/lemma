/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part15
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

def leviSubalgebraComapKerToKer
    {K L G : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing G] [LieAlgebra K G] (q : L →ₗ⁅K⁆ G) (T : LieSubalgebra K G) :
    (leviSubalgebraComapMap q T).ker →ₗ⁅K⁆ q.ker where
  toFun x := ⟨x.1.1, by
    rw [LieHom.mem_ker]
    have hx : leviSubalgebraComapMap q T x.1 = 0 := LieHom.mem_ker.mp x.2
    exact congrArg Subtype.val hx⟩
  map_add' x y := Subtype.ext rfl
  map_smul' a x := Subtype.ext rfl
  map_lie' := by
    intro x y
    apply Subtype.ext
    rfl

end LeviDecomposition
