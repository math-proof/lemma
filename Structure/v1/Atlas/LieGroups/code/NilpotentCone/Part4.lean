/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/NilpotentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Basic
import Mathlib.Topology.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Def.v1.Atlas.LieGroups.code.NilpotentCone.Part5


noncomputable section

open scoped LieAlgebra

open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable {R L}

variable [Module.Finite R L] [Module.Free R L]

section PrincipalSl2

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

structure SubMulFiltrationDomain (R : Type*) [Ring R] where
  v : R → WithBot ℤ
  v_zero : v 0 = ⊥
  v_one : v 1 ≠ ⊥
  v_nonzero : ∀ a : R, a ≠ 0 → v a ≠ ⊥
  v_submul : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b ≤ v (a * b)
  gr_domain : ∀ a b : R, a ≠ 0 → b ≠ 0 → ¬(v a + v b < v (a * b))

structure SubMulFiltration (R : Type*) [Ring R] where
  v : R → WithBot ℤ
  v_zero : v 0 = ⊥
  v_one : v 1 ≠ ⊥
  v_nonzero : ∀ a : R, a ≠ 0 → v a ≠ ⊥
  v_submul : ∀ a b : R, a ≠ 0 → b ≠ 0 → v a + v b ≤ v (a * b)

end PrincipalSl2
end LieAlgebra
end
