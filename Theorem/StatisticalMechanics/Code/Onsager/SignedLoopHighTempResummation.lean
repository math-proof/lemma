/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem ons_setGraphEdgeWeight_self
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex) :
    ons_setGraphEdgeWeight weight edge z edge = z := by
  simp [ons_setGraphEdgeWeight]

@[simp] theorem ons_setGraphEdgeWeight_of_ne
    (weight : Sym2 V → Complex) (edge other : Sym2 V) (z : Complex)
    (hne : other ≠ edge) :
    ons_setGraphEdgeWeight weight edge z other = weight other := by
  simp [ons_setGraphEdgeWeight, hne]

theorem prod_ons_setGraphEdgeWeight_of_mem
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex)
    (F : Finset (Sym2 V)) (hedge : edge ∈ F) :
    ∏ f ∈ F, ons_setGraphEdgeWeight weight edge z f =
      z * ∏ f ∈ F.erase edge, weight f := by
  calc
    ∏ f ∈ F, ons_setGraphEdgeWeight weight edge z f =
        (∏ f ∈ F.erase edge,
          ons_setGraphEdgeWeight weight edge z f) *
            ons_setGraphEdgeWeight weight edge z edge := by
      exact (Finset.prod_erase_mul _ _ hedge).symm
    _ = z * ∏ f ∈ F.erase edge, weight f := by
      rw [ons_setGraphEdgeWeight_self]
      rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro f hf
      exact ons_setGraphEdgeWeight_of_ne weight edge f z
        (Finset.ne_of_mem_erase hf)

theorem prod_ons_setGraphEdgeWeight_of_not_mem
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex)
    (F : Finset (Sym2 V)) (hedge : edge ∉ F) :
    ∏ f ∈ F, ons_setGraphEdgeWeight weight edge z f =
      ∏ f ∈ F, weight f := by
  apply Finset.prod_congr rfl
  intro f hf
  exact ons_setGraphEdgeWeight_of_ne weight edge f z
    (fun h ↦ hedge (h ▸ hf))


end
end StatMech.Onsager
