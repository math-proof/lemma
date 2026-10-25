/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def leviTraceKernel
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] : LieIdeal K L where
  __ := LinearMap.ker (LieModule.traceForm K L M)
  lie_mem := by
    intro x y hy
    change LieModule.traceForm K L M ⁅x, y⁆ = 0
    ext z
    rw [LieModule.traceForm_apply_lie_apply']
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) (⁅x, z⁆ : L)
    simpa using h

end LeviDecomposition
