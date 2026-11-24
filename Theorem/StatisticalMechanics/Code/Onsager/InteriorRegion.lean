module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Def.StatisticalMechanics.Code.Onsager.InteriorRegion


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge


theorem liftS_finite (P : Finset Pt) : (liftS P).Finite :=
  P.finite_toSet.image _


theorem mem_liftS (P : Finset Pt) (q : Pt) : toSite q ∈ liftS P ↔ q ∈ P := by
  constructor
  · rintro ⟨r, hr, hEq⟩
    rw [← toSite_injective hEq]
    exact hr
  · intro h
    exact ⟨q, h, rfl⟩


end StatMech.Onsager.InteriorRegion
