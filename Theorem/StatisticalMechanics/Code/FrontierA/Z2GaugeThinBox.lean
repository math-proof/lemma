/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

section TreeCutSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem cutSpace_eq_edgePowerset_of_isTree [Nonempty V] (hG : G.IsTree) :
    cutSpace G = G.edgeFinset.powerset := by
  have hmaps :
      ((Finset.univ : Finset (ConfigSpace V)) : Set (ConfigSpace V)).MapsTo
        (cutEdges G) (cutSpace G) := by
    intro s _
    change cutEdges G s ∈ cutSpace G
    rw [cutSpace, Finset.mem_image]
    exact ⟨s, Finset.mem_univ s, rfl⟩
  have hfiber : ∀ delta ∈ cutSpace G,
      ((Finset.univ.filter
        (fun s : ConfigSpace V => cutEdges G s = delta)).card) = 2 := by
    intro delta hdelta
    rw [cutSpace, Finset.mem_image] at hdelta
    obtain ⟨s, _, hs⟩ := hdelta
    exact fiber_card_eq_two G hG.preconnected hs
  have hcutCard : 2 * (cutSpace G).card =
      Fintype.card (ConfigSpace V) := by
    have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ] at hpartition
    calc
      2 * (cutSpace G).card =
          ∑ delta ∈ cutSpace G, 2 := by
            simp [mul_comm]
      _ = ∑ delta ∈ cutSpace G,
          (Finset.univ.filter
            (fun s : ConfigSpace V => cutEdges G s = delta)).card := by
            apply Finset.sum_congr rfl
            intro delta hdelta
            exact (hfiber delta hdelta).symm
      _ = Fintype.card (ConfigSpace V) := hpartition.symm
  have hpowerCard : 2 * G.edgeFinset.powerset.card =
      Fintype.card (ConfigSpace V) := by
    rw [Finset.card_powerset, Fintype.card_fun, Fintype.card_bool]
    rw [← hG.card_edgeFinset]
    simp [pow_succ']
  have hcard : (cutSpace G).card = G.edgeFinset.powerset.card := by
    omega
  apply Finset.eq_of_subset_of_card_le
  · intro delta hdelta
    rw [Finset.mem_powerset]
    rw [cutSpace, Finset.mem_image] at hdelta
    obtain ⟨s, _, rfl⟩ := hdelta
    exact Finset.filter_subset _ _
  · exact hcard.ge

end TreeCutSpace
end
end StatMech.FrontierA
