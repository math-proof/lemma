/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part12
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

def leviTheta
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) :
    I →ₗ[K] leviHomScalarMaps I where
  toFun x := ⁅(x.1 : L), f⁆
  map_add' x y := by rw [Submodule.coe_add, add_lie]
  map_smul' a x := by
    change ⁅((a • x).1 : L), f⁆ = (RingHom.id K) a • ⁅(x.1 : L), f⁆
    rw [RingHom.id_apply, SetLike.val_smul, smul_lie]

end LeviDecomposition
