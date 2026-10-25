/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.DualCutToPath.Part4
import Def.StatisticalMechanics.Code.Universality.PlanarDualCutConnected.Part3
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


@[simp] theorem pdc_rot90InvHom_apply (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (p : Site 2) :
    pdc_rot90InvHom ω n p = rot90Inv p := rfl


theorem pdc_rot90Inv_rot90Fun (x : Site 2) : rot90Inv (rot90Fun x) = x := by
  funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]


theorem pdc_dualReach_of_primalReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {a b : Site 2} (h : (pdc_barrierGraphPrimal ω n).Reachable a b) :
    (dcw_dualBarrierGraph ω n).Reachable (rot90Fun a) (rot90Fun b) := by
  have := h.map (pdc_rot90Hom ω n)
  simpa using this


theorem pdc_primalReach_of_dualReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Reachable p q) :
    (pdc_barrierGraphPrimal ω n).Reachable (rot90Inv p) (rot90Inv q) := by
  have := h.map (pdc_rot90InvHom ω n)
  simpa using this


theorem pdc_dualReach_iff_primalReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (a b : Site 2) :
    (dcw_dualBarrierGraph ω n).Reachable (rot90Fun a) (rot90Fun b) ↔
      (pdc_barrierGraphPrimal ω n).Reachable a b := by
  constructor
  · intro h
    have := pdc_primalReach_of_dualReach ω n h
    rwa [pdc_rot90Inv_rot90Fun a, pdc_rot90Inv_rot90Fun b] at this
  · exact pdc_dualReach_of_primalReach ω n


end Universality
end StatMech
