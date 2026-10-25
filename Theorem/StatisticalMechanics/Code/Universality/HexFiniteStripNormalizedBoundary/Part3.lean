/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Structure.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

theorem hexStripDirMids_final_mem (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum m h ts, hexInfra_headAccum h ts) ∈
      hexStripDirMids m h ts := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih =>
      rw [hexStripDirMids_cons]
      exact List.mem_cons_of_mem _
        (ih (m + halfStep h + halfStep (h + t)) (h + t))


theorem hexStart_midsAux_prefix (m : ℂ) (h : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) : midsAux m h s <+: midsAux m h ts := by
  obtain ⟨u, rfl⟩ := hst
  induction s generalizing m h with
  | nil =>
      cases u <;> simp [midsAux]
  | cons t s ih =>
      rw [List.cons_append, midsAux_cons, midsAux_cons]
      exact (List.prefix_cons_inj _).mpr
        (ih (m + halfStep h + halfStep (h + t)) (h + t))


theorem hexStart_verticesAux_prefix (m : ℂ) (h : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) : verticesAux m h s <+: verticesAux m h ts := by
  obtain ⟨u, rfl⟩ := hst
  induction s generalizing m h with
  | nil =>
      cases u <;> simp [verticesAux]
  | cons t s ih =>
      rw [List.cons_append, verticesAux_cons, verticesAux_cons]
      exact (List.prefix_cons_inj _).mpr
        (ih (m + halfStep h + halfStep (h + t)) (h + t))


theorem hexStart_isLegalSAW_of_prefix (a : ℂ) (h0 : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns a h0 s).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact hlegal.1 t (hst.sublist.mem ht)
  · change (verticesAux a h0 s).Nodup
    have hsaw := hlegal.2
    change (verticesAux a h0 ts).Nodup at hsaw
    exact hsaw.sublist (hexStart_verticesAux_prefix a h0 hst).sublist


theorem hexStart_staysIn_of_prefix
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) {s ts : List ℤ}
    (hst : s <+: ts) (hstay : (ofTurns a h0 ts).StaysIn inRegion) :
    (ofTurns a h0 s).StaysIn inRegion := by
  intro m hm
  apply hstay m
  change m ∈ midsAux a h0 s at hm
  change m ∈ midsAux a h0 ts
  exact (hexStart_midsAux_prefix a h0 hst).sublist.mem hm


theorem hexStripDirMids_mem_prefix_state
    (m : ℂ) (h : ℤ) (ts : List ℤ) (p : ℂ × ℤ)
    (hp : p ∈ hexStripDirMids m h ts) :
    ∃ s : List ℤ, s <+: ts ∧
      p = (hexInfra_midAccum m h s, hexInfra_headAccum h s) := by
  induction ts generalizing m h with
  | nil =>
      simp only [hexStripDirMids_nil, List.mem_singleton] at hp
      subst p
      exact ⟨[], ⟨[], rfl⟩, rfl⟩
  | cons t ts ih =>
      rw [hexStripDirMids_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨[], ⟨t :: ts, rfl⟩, rfl⟩
      · obtain ⟨s, hs, rfl⟩ :=
          ih (m + halfStep h + halfStep (h + t)) (h + t) hp
        refine ⟨t :: s, ?_, ?_⟩
        · exact (List.prefix_cons_inj t).mpr hs
        · rfl


end HexFiniteRegion
end StatMech.Universality
