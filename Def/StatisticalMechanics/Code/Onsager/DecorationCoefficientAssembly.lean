/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2
import Structure.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


noncomputable def ons_decoratedEdgeSplit
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (D : ons_DecoratedContainingEdge L d) :
    ons_DecoratedEdgeSplit L d D := by
  let hex := ons_decorated_split_cycle_at_external L D.1 d D.2
  let q := Classical.choose hex
  let hexR := Classical.choose_spec hex
  let R := Classical.choose hexR
  have hs := Classical.choose_spec hexR
  exact ⟨q, R, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
    hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2⟩


end StatMech.Onsager
