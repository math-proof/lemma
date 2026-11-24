module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Def.Algebra.Lie.LeviDecomposition.Part4


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

theorem levi_scalar_unique
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) (hW : W ≠ ⊥) {a b : K}
    (h : ∀ w : W, a • w = b • w) : a = b := by
  have hWsub : W.toSubmodule ≠ ⊥ := by
    intro h
    apply hW
    rw [← LieSubmodule.toSubmodule_inj]
    exact h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWsub
  have hab : a • w = b • w := congrArg Subtype.val (h ⟨w, hw⟩)
  have hz : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hw0)

end LeviDecomposition
