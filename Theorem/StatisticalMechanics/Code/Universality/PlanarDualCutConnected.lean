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
import Def.StatisticalMechanics.Code.Universality.PlanarDualCutConnected
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


@[simp] theorem pdc_barrierGraphPrimal_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (a b : Site 2) :
    (pdc_barrierGraphPrimal ω n).Adj a b ↔
      ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
        ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) := Iff.rfl


theorem pdc_rot90_adj_dual (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {a b : Site 2}
    (h : (pdc_barrierGraphPrimal ω n).Adj a b) :
    (dcw_dualBarrierGraph ω n).Adj (rot90Fun a) (rot90Fun b) := by
  obtain ⟨v, w, hvw, hab⟩ := h
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨v, w, hvw, Or.inl ⟨by rw [ha], by rw [hb]⟩⟩
  · exact ⟨v, w, hvw, Or.inr ⟨by rw [ha], by rw [hb]⟩⟩


end Universality
end StatMech
