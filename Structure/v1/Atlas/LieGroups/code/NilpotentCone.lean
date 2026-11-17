/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/NilpotentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Rank
public import Mathlib.Algebra.Lie.CartanExists
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Def.v1.Atlas.LieGroups.code.NilpotentCone


public noncomputable section

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
