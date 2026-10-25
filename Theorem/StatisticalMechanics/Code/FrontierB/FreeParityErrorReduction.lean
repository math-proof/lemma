/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal.Part2
import Mathlib.Algebra.BigOperators.Ring.Nat
import Def.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction
open Set
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} (G : SimpleGraph V)

theorem clusterMarkCount_union (omega : ConfigSpace (Sym2 V))
    [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B)
    (C : (openSub G omega).ConnectedComponent) :
    clusterMarkCount G omega (A ∪ B) C =
      clusterMarkCount G omega A C + clusterMarkCount G omega B C := by
  classical
  unfold clusterMarkCount
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hdisj)

theorem sum_clusterMarkCount_markedComponents
    (omega : ConfigSpace (Sym2 V)) (A : Finset V) :
    ∑ C ∈ markedComponents G omega A, clusterMarkCount G omega A C = A.card := by
  classical
  have hmaps : ∀ x ∈ A,
      (openSub G omega).connectedComponentMk x ∈ markedComponents G omega A := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : Nat))
  simpa [markedComponents, clusterMarkCount] using hsum

theorem mem_markedComponents_of_odd_clusterMarkCount
    (omega : ConfigSpace (Sym2 V)) (A : Finset V)
    (C : (openSub G omega).ConnectedComponent)
    (hodd : Odd (clusterMarkCount G omega A C)) :
    C ∈ markedComponents G omega A := by
  classical
  have hpos : 0 < clusterMarkCount G omega A C :=
    Nat.pos_of_ne_zero (fun hzero => by simp [hzero] at hodd)
  rw [clusterMarkCount, Finset.card_pos] at hpos
  obtain ⟨x, hx⟩ := hpos
  rw [Finset.mem_filter] at hx
  exact Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩


end StatMech.FK
