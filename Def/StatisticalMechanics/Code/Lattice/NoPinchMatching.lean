/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

def npm_KingSaturated (K : Set (Site 2)) : Prop :=
  ∀ f : Site 2,
    (npd_P00 f ∈ K → npd_P11 f ∈ K → (npd_P10 f ∈ K ∨ npd_P01 f ∈ K)) ∧
    (npd_P10 f ∈ K → npd_P01 f ∈ K → (npd_P00 f ∈ K ∨ npd_P11 f ∈ K))


end Lattice
end StatMech
