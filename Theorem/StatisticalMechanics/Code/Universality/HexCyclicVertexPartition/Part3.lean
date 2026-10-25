/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexCyclic_staysIn_concat_single_iff
    (region : ℂ → Prop) (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).StaysIn region ↔
      (ofTurns a h0 ts).StaysIn region ∧
        region (hexCyclicNewMid a h0 ts t) := by
  change (∀ m, m ∈ midsAux a h0 (ts ++ [t]) → region m) ↔
    (∀ m, m ∈ midsAux a h0 ts → region m) ∧
      region (hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + t))
  rw [hexCyclic_midsAux_append_single]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro m hm
      exact h m (List.mem_append_left _ hm)
    · exact h _ (List.mem_append_right _ (by simp))
  · rintro ⟨hbase, hnew⟩ m hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact hbase m hm
    · simp only [List.mem_singleton] at hm
      subst m
      exact hnew


theorem hexCyclic_isSAW_concat_single_iff
    (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).IsSAW ↔
      (ofTurns a h0 ts).IsSAW ∧
        hexCyclicNewVertex a h0 ts t ∉ (ofTurns a h0 ts).vertices := by
  change (verticesAux a h0 (ts ++ [t])).Nodup ↔
    (verticesAux a h0 ts).Nodup ∧
      (hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + t) +
        halfStep (hexInfra_headAccum h0 ts + t)) ∉ verticesAux a h0 ts
  rw [hexCyclic_verticesAux_append_single]
  rw [List.nodup_append]
  constructor
  · rintro ⟨hbase, _, hdisj⟩
    refine ⟨hbase, ?_⟩
    intro hmem
    exact hdisj _ hmem _ (by simp) rfl
  · rintro ⟨hbase, hfresh⟩
    refine ⟨hbase, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact fun hxy => hfresh (hxy ▸ hx)


theorem hexCyclic_legalTurns_concat_single
    (a : ℂ) (h0 t : ℤ) (ts : List ℤ)
    (hbase : (ofTurns a h0 ts).LegalTurns) (ht : t = 1 ∨ t = -1) :
    (ofTurns a h0 (ts ++ [t])).LegalTurns := by
  intro u hu
  simp only [ofTurns_turns, List.mem_append, List.mem_singleton] at hu ⊢
  rcases hu with hu | rfl
  · exact hbase u hu
  · exact ht


end
end StatMech.Universality
