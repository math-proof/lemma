/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theorem.Algebra.Lie.LeviDecomposition.Part2

@[expose] public section

/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def leviCasimir
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Free K M] [Module.Finite K M]
    (hβ : (LieModule.traceForm K L M).Nondegenerate) : Module.End K M := by
  classical
  let b := Module.Free.chooseBasis K L
  exact ∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)

end LeviDecomposition
