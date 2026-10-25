/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentAssociationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneFiber
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedGateShift
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamComponentAssociationReduction
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamCutPairCorrelation_monotone
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (x y : V) :
    Monotone (grahamCutPairCorrelation G beta J x y) := by
  intro S T hST
  unfold grahamCutPairCorrelation
  by_cases hxyS : x ∈ S ∧ y ∈ S
  · have hxyT : x ∈ T ∧ y ∈ T := ⟨hST hxyS.1, hST hxyS.2⟩
    rw [if_pos hxyS, if_pos hxyT]
    have hmono := expectationJ_couplingIn_le G beta (couplingIn J T) hbeta
      (fun e => by
        unfold couplingIn
        split <;> simp_all [hJ e]) S {x, y}
    rwa [couplingIn_couplingIn_of_subset J hST] at hmono
  · rw [if_neg hxyS]
    by_cases hxyT : x ∈ T ∧ y ∈ T
    · rw [if_pos hxyT]
      exact Ising.acr_expectationJ_nonneg G beta (couplingIn J T) hbeta
        (fun e => by
          unfold couplingIn
          split <;> simp_all [hJ e]) {x, y}
    · simp [hxyT]


end StatMech.FrontierA
