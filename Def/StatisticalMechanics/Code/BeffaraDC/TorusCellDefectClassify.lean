/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellComplement
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


def torusCellEdgeStraddles {V : Type*} (S : Set V) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun x y => (x ∈ S ↔ y ∉ S), by
    intro x y
    simp only [eq_iff_iff]
    tauto⟩ e

end StatMech.BeffaraDC
