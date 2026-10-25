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
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


def pdc_barrierGraphPrimal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    SimpleGraph (Site 2) where
  Adj a b :=
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧
      ((a = v ∧ b = w) ∨ (a = w ∧ b = v))
  symm := by
    constructor
    rintro a b ⟨v, w, hvw, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩
    · exact ⟨v, w, hvw, Or.inr ⟨hb, ha⟩⟩
    · exact ⟨v, w, hvw, Or.inl ⟨hb, ha⟩⟩
  loopless := by
    refine ⟨fun a ha => ?_⟩
    rcases ha with ⟨v, w, hvw, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩
    · rw [ha] at hb
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 hb
    · rw [ha] at hb
      exact (hypercubicLattice 2).ne_of_adj hvw.2.2.2 hb.symm

end Universality
end StatMech
