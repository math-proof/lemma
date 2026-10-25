/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part4
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ons_setGraphEdgeWeightList_apply
    (weight : Sym2 V → Complex) (z : Complex)
    (edges : List (Sym2 V)) (edge : Sym2 V) :
    ons_setGraphEdgeWeightList weight z edges edge =
      if edge ∈ edges then z else weight edge := by
  induction edges with
  | nil => simp [ons_setGraphEdgeWeightList]
  | cons first rest ih =>
      by_cases hfirst : edge = first
      · subst first
        simp [ons_setGraphEdgeWeightList]
      · simp [ons_setGraphEdgeWeightList, hfirst, ih]

theorem ons_setGraphEdgeWeight_comm
    (weight : Sym2 V → Complex) (e f : Sym2 V) (z w : Complex)
    (hef : e ≠ f) :
    ons_setGraphEdgeWeight (ons_setGraphEdgeWeight weight e z) f w =
      ons_setGraphEdgeWeight (ons_setGraphEdgeWeight weight f w) e z := by
  funext edge
  by_cases he : edge = e
  · subst edge
    simp [ons_setGraphEdgeWeight, hef]
  · by_cases hf : edge = f
    · subst edge
      simp [ons_setGraphEdgeWeight, he]
    · simp [ons_setGraphEdgeWeight, he, hf]

theorem ons_setGraphEdgeWeightList_set_comm
    (weight : Sym2 V → Complex) (edge : Sym2 V)
    (z w : Complex) (edges : List (Sym2 V))
    (hedge : edge ∉ edges) :
    ons_setGraphEdgeWeightList
        (ons_setGraphEdgeWeight weight edge z) w edges =
      ons_setGraphEdgeWeight
        (ons_setGraphEdgeWeightList weight w edges) edge z := by
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.mem_cons, not_or] at hedge
      simp only [ons_setGraphEdgeWeightList]
      rw [ih hedge.2,
        ons_setGraphEdgeWeight_comm _ edge first z w hedge.1]


end
end StatMech.Onsager
