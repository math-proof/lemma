/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Def.StatisticalMechanics.Code.Sharpness.ABGhostRegularity
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

section FiniteProduct

variable {E : Type*} [Fintype E] [DecidableEq E]


@[simp] theorem abgrMerge_mem (s : Finset E) (gamma : {e // e ∈ s} -> Bool)
    (eta : {e // e ∉ s} -> Bool) (e : {e // e ∈ s}) :
    abgrMerge s gamma eta e = gamma e := by
  simp [abgrMerge]

@[simp] theorem abgrMerge_notMem (s : Finset E) (gamma : {e // e ∈ s} -> Bool)
    (eta : {e // e ∉ s} -> Bool) (e : {e // e ∉ s}) :
    abgrMerge s gamma eta e = eta e := by
  change (if h : (e : E) ∈ s then gamma ⟨e, h⟩ else eta ⟨e, h⟩) = eta e
  rw [dif_neg e.property]

set_option maxHeartbeats 800000 in


theorem abgr_probV_split (s : Finset E) (q : Real) (p : E -> Real)
    (A : Set (ConfigSpace E)) :
    probV (paramOn s q p) A =
      ∑ eta : {e // e ∉ s} -> Bool,
        (∏ e : {e // e ∉ s}, if eta e then p e else 1 - p e) *
          probV (fun _ : {e // e ∈ s} => q)
            {gamma | abgrMerge s gamma eta ∈ A} := by
  unfold probV
  rw [← Equiv.sum_comp
    (Equiv.piEquivPiSubtypeProd (fun e : E => e ∈ s) (fun _ => Bool)).symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eta _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro gamma _
  rw [configWeightV_paramOn_factor]
  unfold configWeightV edgeWeightV
  rw [Finset.prod_subtype (p := fun e : E => e ∈ s) s (by simp)]
  rw [Finset.prod_subtype (p := fun e : E => e ∉ s) (Finset.univ \ s) (by simp)]
  change
    A.indicator (fun _ => (1 : Real)) (abgrMerge s gamma eta) *
        ((∏ e : {e // e ∈ s}, if abgrMerge s gamma eta e then q else 1 - q) *
          (∏ e : {e // e ∉ s},
            if abgrMerge s gamma eta e then p e else 1 - p e)) =
      (∏ e : {e // e ∉ s}, if eta e then p e else 1 - p e) *
        ({gamma | abgrMerge s gamma eta ∈ A}.indicator (fun _ => (1 : Real)) gamma *
          ∏ e : {e // e ∈ s}, if gamma e then q else 1 - q)
  simp only [abgrMerge_mem, abgrMerge_notMem]
  by_cases hA : abgrMerge s gamma eta ∈ A <;> simp [hA] <;> ring

end FiniteProduct
end Sharpness
end StatMech
