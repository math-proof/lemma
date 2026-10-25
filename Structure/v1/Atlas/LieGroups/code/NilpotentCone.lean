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
import Def.v1.Atlas.LieGroups.code.NilpotentCone


noncomputable section

open scoped LieAlgebra

open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

structure AdjointGroupAction where
  G : Type*
  instGroup : Group G
  Ad : G → L ≃ₗ⁅R⁆ L
  Ad_mul : ∀ g₁ g₂ : G,
    (Ad (@HMul.hMul G G G (@instHMul G instGroup.toMul) g₁ g₂) : L → L) =
    (Ad g₁ : L → L) ∘ (Ad g₂ : L → L)
  Ad_one : Ad (@One.one G instGroup.toOne) = LieEquiv.refl
  instTopologicalSpaceG : TopologicalSpace G
  instIrreducibleSpaceG : @IrreducibleSpace G instTopologicalSpaceG
  orbit_map_continuous : ∀ (ts : TopologicalSpace L) (x : L),
    @Continuous G L instTopologicalSpaceG ts (fun g => Ad g x)

end LieAlgebra
end
