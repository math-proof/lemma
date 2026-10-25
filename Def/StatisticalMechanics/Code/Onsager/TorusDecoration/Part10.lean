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
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part9


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

noncomputable def ons_portPatternOfDecorated (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L)) : ons_PortPattern L where
  bit := ons_decoratedPortBit D
  rev_bit := by
    intro d
    have hinv : ons_dartRev L (ons_dartRev L d) = d :=
      ons_dartRev_involutive L d
    have hedge : s(ons_dartRev L d, ons_dartRev L (ons_dartRev L d)) =
        s(d, ons_dartRev L d) := by
      rw [hinv]
      exact Sym2.eq_swap
    simp only [ons_decoratedPortBit, hedge]
  site_even := by
    intro s
    exact ons_decChainEven_port_even (ons_decorated_local_even L D hD s)

end StatMech.Onsager
