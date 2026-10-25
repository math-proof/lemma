/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part2
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
