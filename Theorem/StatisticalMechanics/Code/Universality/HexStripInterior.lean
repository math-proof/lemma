/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Def.StatisticalMechanics.Code.Universality.HexStripInterior


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


@[simp] theorem hexStripDirMids_nil (m : ℂ) (h : ℤ) : hexStripDirMids m h [] = [(m, h)] := rfl

@[simp] theorem hexStripDirMids_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    hexStripDirMids m h (t :: ts)
      = (m, h) :: hexStripDirMids (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts :=
  rfl


theorem hexStrip_nonlast_dir (m : ℂ) (h : ℤ) (ts : List ℤ) (v : ℂ)
    (hv : v ∈ HexWalk.verticesAux m h ts)
    (hvne : v ≠ hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)) :
    ∃ (m' : ℂ) (h' t' : ℤ),
        (m', h') ∈ hexStripDirMids m h ts
      ∧ (m' + HexWalk.halfStep h' + HexWalk.halfStep (h' + t'), h' + t')
          ∈ hexStripDirMids m h ts
      ∧ v = m' + HexWalk.halfStep h'
      ∧ t' ∈ ts := by
  induction ts generalizing m h with
  | nil =>
    rw [HexWalk.verticesAux_nil, List.mem_singleton] at hv
    rw [hexInfra_midAccum_nil, hexInfra_headAccum_nil] at hvne
    exact absurd hv hvne
  | cons t ts ih =>
    rw [HexWalk.verticesAux_cons, List.mem_cons] at hv
    rcases hv with hhead | htail
    · 
      refine ⟨m, h, t, ?_, ?_, hhead, List.mem_cons_self⟩
      · rw [hexStripDirMids_cons]; exact List.mem_cons_self
      · rw [hexStripDirMids_cons]
        refine List.mem_cons_of_mem _ ?_
        cases ts with
        | nil => rw [hexStripDirMids_nil]; exact List.mem_singleton.mpr rfl
        | cons s ss => rw [hexStripDirMids_cons]; exact List.mem_cons_self
    · 
      rw [hexInfra_midAccum_cons, hexInfra_headAccum_cons] at hvne
      obtain ⟨m', h', t', hm1, hm2, hveq, ht'⟩ := ih _ _ htail hvne
      refine ⟨m', h', t', ?_, ?_, hveq, List.mem_cons_of_mem _ ht'⟩
      · rw [hexStripDirMids_cons]; exact List.mem_cons_of_mem _ hm1
      · rw [hexStripDirMids_cons]; exact List.mem_cons_of_mem _ hm2


end StatMech.Universality
