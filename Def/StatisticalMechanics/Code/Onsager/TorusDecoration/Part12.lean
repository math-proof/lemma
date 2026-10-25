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
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part11


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

noncomputable def ons_evenSubgraphPortEquiv (L : ℕ) [Fact (2 < L)] :
    {F : Finset (Sym2 (ZMod L × ZMod L)) //
      F ∈ evenSubgraphs (onsTorusGraph L)} ≃ ons_PortPattern L where
  toFun F := ons_evenSubgraphPortPattern L F.1 F.2
  invFun P := ⟨ons_portPatternEdges L P, ons_portPatternEdges_even L P⟩
  left_inv F := Subtype.ext (ons_portPatternEdges_evenSubgraphPortPattern L F.1 F.2)
  right_inv P := ons_evenSubgraphPortPattern_portPatternEdges L P

end StatMech.Onsager
