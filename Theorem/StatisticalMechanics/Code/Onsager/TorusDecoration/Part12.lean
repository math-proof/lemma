/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part12


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_portPatternOfDecorated_decoratedEdges
    (L : ℕ) [Fact (2 < L)] (P : ons_PortPattern L) :
    ons_portPatternOfDecorated L (ons_decoratedEdges P)
      (ons_decoratedEdges_even L P) = P := by
  apply ons_PortPattern.ext
  funext d
  have hedge : s(d, ons_dartRev L d) ∈ (ons_decGraph L).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact Or.inl rfl
  simp only [ons_portPatternOfDecorated, ons_decoratedPortBit,
    ons_decoratedEdges, Finset.mem_filter, hedge, true_and,
    ons_decEdgeBit_external, ons_fin2_indicator_eq]


end StatMech.Onsager
