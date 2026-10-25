/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Def.StatisticalMechanics.Code.Universality.DualCutToPath
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem dcp_route_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) : dcw_BarrierRoute ω n :=
  hcut


theorem dcp_dualVerticalCrossing_of_cutConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hcut : dcp_DualCutConnects ω n) :
    DualVerticalCrossing ω 0 n 0 n :=
  dcw_dualVerticalCrossing_of_route ω n (dcp_route_of_cutConnects ω n hcut)


theorem dcp_dichotomy_of_cutConnects (n : ℤ)
    (hcut : ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ HorizontalCrossing ω 0 n 0 n → dcp_DualCutConnects ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n :=
  dcw_square_dichotomy n (fun ω hω => dcp_route_of_cutConnects ω n (hcut ω hω))


theorem dcp_bottomBarrierVertex_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v : Site 2, v 1 = 0 ∧ (∃ q, (dcw_dualBarrierGraph ω n).Adj (rot90Fun v) q) := by
  obtain ⟨v, w, hbar, hv0, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact ⟨v, hv0, rot90Fun w, v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩


theorem dcp_topBarrierVertex_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v : Site 2, v 1 = n ∧ (∃ q, (dcw_dualBarrierGraph ω n).Adj (rot90Fun v) q) := by
  obtain ⟨v, w, hbar, hvn, _⟩ := dcp_topBarrierEdge_exists ω n hn hnoH
  exact ⟨v, hvn, rot90Fun w, v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩


theorem dcp_rot90_bottomRow (a : ℤ) : rot90Fun ![a, 0] = ![0, a] := by
  simp


theorem dcp_rot90_topRow (a n : ℤ) : rot90Fun ![a, n] = ![-n, a] := by
  simp


end Universality
end StatMech
