/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part4
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]

variable [DecidableEq Vin] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (iota : Vin -> Vout)

variable (bdryOut : Vout -> Prop) [DecidablePred bdryOut]


theorem ocd_psiEdgeFactorW_pos {pfOut : Sym2 Vout -> Real}
    (hpf : forall e, 0 < pfOut e) (hpf1 : forall e, pfOut e < 1)
    (psi : ConfigSpace (Sym2 Vout)) :
    0 < ocd_psiEdgeFactorW Gout iota pfOut psi := by
  unfold ocd_psiEdgeFactorW
  apply Finset.prod_pos
  intro e he
  split
  · exact hpf e
  · linarith [hpf1 e]


theorem ocd_edgeProductW_psiExt (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {pfIn : Sym2 Vin -> Real} {pfOut : Sym2 Vout -> Real}
    (hparam : ocd_ParamCompatible iota pfIn pfOut)
    (psi : ConfigSpace (Sym2 Vout)) (omega : ConfigSpace (Sym2 Vin)) :
    edgeProductW Gout pfOut (ocd_psiExt iota psi omega) =
      edgeProductW Gin pfIn omega *
        ocd_psiEdgeFactorW Gout iota pfOut psi := by
  classical
  unfold edgeProductW ocd_psiEdgeFactorW
  rw [← Finset.prod_filter_mul_prod_filter_not Gout.edgeFinset
    (fun e => e ∈ Set.range (ocd_innerEdge iota))]
  congr 1
  · rw [← ocd_innerEdge_image_edgeFinset hiota hadjm,
      Finset.prod_image
        (fun a _ b _ h => ocd_innerEdge_injective iota hiota h)]
    refine Finset.prod_congr rfl (fun e he => ?_)
    rw [ocd_psiExt_innerEdge hiota, ← hparam e]
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    rw [ocd_psiExt_eq_psi_of_not_range psi omega he.2]


end FK
end StatMech
