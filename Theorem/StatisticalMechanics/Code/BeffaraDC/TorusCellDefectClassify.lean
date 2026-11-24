module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellComplement
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
public import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


@[simp] theorem torusCellEdgeStraddles_mk {V : Type*} (S : Set V) (x y : V) :
    torusCellEdgeStraddles S s(x, y) ↔ (x ∈ S ↔ y ∉ S) := Iff.rfl


end StatMech.BeffaraDC
