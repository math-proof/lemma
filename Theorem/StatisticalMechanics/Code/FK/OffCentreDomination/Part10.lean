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
import Def.StatisticalMechanics.Code.FK.OffCentreDomination.Part14
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

theorem ocd_psiEdgeFactor_pos (hp : 0 < p) (hp1 : p < 1) :
    0 < ocd_psiEdgeFactor Gout ιV ψ p := by
  unfold ocd_psiEdgeFactor
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith


theorem ocd_edgeProduct_psiExt (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p : ℝ} (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    edgeProduct Gout p (ocd_psiExt ιV ψ ω)
      = edgeProduct Gin p ω * ocd_psiEdgeFactor Gout ιV ψ p := by
  classical
  unfold edgeProduct ocd_psiEdgeFactor
  rw [← Finset.prod_filter_mul_prod_filter_not Gout.edgeFinset
    (fun e => e ∈ Set.range (ocd_innerEdge ιV))]
  congr 1
  · rw [← ocd_innerEdge_image_edgeFinset hι hadjm,
      Finset.prod_image (fun a _ b _ h => ocd_innerEdge_injective ιV hι h)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [ocd_psiExt_innerEdge hι]
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    rw [ocd_psiExt_eq_psi_of_not_range ψ ω he.2]


end FK
end StatMech
