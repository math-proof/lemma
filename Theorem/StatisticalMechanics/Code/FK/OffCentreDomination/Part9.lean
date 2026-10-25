/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.LimitCommutation.Part5
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Def.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin] [Fintype Vout] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (ιV : Vin → Vout)


variable {Gin Gout ιV}

variable (Gin Gout ιV)

variable (bdryOut : Vout → Prop) [DecidablePred bdryOut]


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

theorem ocd_numClustersBC_psiExt (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    numClustersBC Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) (ocd_psiExt ιV ψ ω)
      = numClustersBC Gin (ocd_inducedWiring Gout ιV bdryOut ψ) ω
          + ocd_outsideShift Gout ιV bdryOut ψ := by
  have hfull : numClustersBC Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) (ocd_psiExt ιV ψ ω)
      = Nat.card (ocd_fullGraph Gout ιV bdryOut ω ψ).ConnectedComponent := by
    rw [numClustersBC, ← ocd_fullGraph]
  have hinner : numClustersBC Gin (ocd_inducedWiring Gout ιV bdryOut ψ) ω
      = Nat.card (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).ConnectedComponent := by
    rw [numClustersBC, ← ocd_innerGraph]
  rw [hfull, hinner, ocd_outsideShift,
    ← Nat.card_congr (ocd_fullComponentEquiv hι hadjm ω ψ), Nat.card_sum]


theorem ocd_innerEdge_image_edgeFinset (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) :
    Gin.edgeFinset.image (ocd_innerEdge ιV)
      = Gout.edgeFinset.filter (· ∈ Set.range (ocd_innerEdge ιV)) := by
  ext e
  simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_edgeFinset, Set.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, a, rfl⟩
    induction a using Sym2.ind with | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at ha
    rw [ocd_innerEdge_mk, SimpleGraph.mem_edgeSet, ← hadjm]
    exact ha
  · rintro ⟨hmem, a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    induction a using Sym2.ind with | _ x y =>
    rw [ocd_innerEdge_mk, SimpleGraph.mem_edgeSet] at hmem
    rw [SimpleGraph.mem_edgeSet, hadjm]
    exact hmem


end FK
end StatMech
