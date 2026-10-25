/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part10


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_augmentedPair_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_augmentedPair ts hleg).1.length +
        (hlhda_augmentedPair ts hleg).2.length = ts.length + 4 := by
  rw [hlhda_augmentedPair, hlhda_prefixAugment_length,
    hlhda_suffixAugment_length]
  have hcple := hlhda_cutPos_le ts hleg
  simp only [List.length_drop]
  omega

theorem hlhda_augmentedPair_injective
    {xs ys : List ℤ}
    (hx : (ofTurns hexAWStart 1 xs).IsLegalSAW)
    (hy : (ofTurns hexAWStart 1 ys).IsLegalSAW)
    (heq : hlhda_augmentedPair xs hx = hlhda_augmentedPair ys hy) :
    xs = ys := by
  let cpx := hlhda_cutPos xs hx
  let cpy := hlhda_cutPos ys hy
  let px := xs.take cpx
  let py := ys.take cpy
  have hpreCode : hlhda_reverseCode px = hlhda_reverseCode py := by
    have hfst := congrArg Prod.fst heq
    rw [hlhda_augmentedPair, hlhda_augmentedPair,
      hlhda_prefixAugment_eq_reverseCode,
      hlhda_prefixAugment_eq_reverseCode] at hfst
    exact hfst
  have hxpreLegal : ∀ t ∈ px, t = 1 ∨ t = -1 := by
    intro t ht
    exact hx.1 t (List.mem_of_mem_take ht)
  have hypreLegal : ∀ t ∈ py, t = 1 ∨ t = -1 := by
    intro t ht
    exact hy.1 t (List.mem_of_mem_take ht)
  have hxpreIn : px ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base px).dir := by
    intro hpx
    have hxne : xs ≠ [] := by intro hnil; simp [px, hnil] at hpx
    simpa [px, cpx, hlhda_cutState] using hlhda_cutState_inward hx hxne
  have hypreIn : py ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base py).dir := by
    intro hpy
    have hyne : ys ≠ [] := by intro hnil; simp [py, hnil] at hpy
    simpa [py, cpy, hlhda_cutState] using hlhda_cutState_inward hy hyne
  have hpre : px = py := hlhda_reverseCode_injective hxpreLegal
    hypreLegal hxpreIn hypreIn hpreCode
  have hpxLen : px.length = cpx := by
    simp [px, cpx, List.length_take_of_le (hlhda_cutPos_le xs hx)]
  have hpyLen : py.length = cpy := by
    simp [py, cpy, List.length_take_of_le (hlhda_cutPos_le ys hy)]
  have hcp : cpx = cpy := by rw [← hpxLen, ← hpyLen, hpre]
  by_cases hpxNil : px = []
  · have hxNil : xs = [] := by
      by_contra hxne
      have hcpos := hlhda_cutPos_pos hx hxne
      have hlen := congrArg List.length hpxNil
      rw [hpxLen] at hlen
      simp at hlen
      change 0 < cpx at hcpos
      omega
    have hpyNil : py = [] := hpre ▸ hpxNil
    have hyNil : ys = [] := by
      by_contra hyne
      have hcpos := hlhda_cutPos_pos hy hyne
      have hlen := congrArg List.length hpyNil
      rw [hpyLen] at hlen
      simp at hlen
      change 0 < cpy at hcpos
      omega
    rw [hxNil, hyNil]
  · have hxne : xs ≠ [] := by intro hnil; simp [px, hnil] at hpxNil
    have hyne : ys ≠ [] := by
      intro hnil
      have : py = [] := by simp [py, hnil]
      exact hpxNil (hpre.trans this)
    let r := hlhda_cutState xs hx
    have hr : hlhda_cutState ys hy = r := by
      dsimp [r, hlhda_cutState]
      change hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base py =
        hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base px
      rw [hpre]
    let sx := xs.drop cpx
    let sy := ys.drop cpy
    have hsufCode : hlhda_forwardCode r.dir sx =
        hlhda_forwardCode r.dir sy := by
      have hsnd := congrArg Prod.snd heq
      rw [hlhda_augmentedPair, hlhda_augmentedPair,
        hlhda_suffixAugment_eq_forwardCode,
        hlhda_suffixAugment_eq_forwardCode] at hsnd
      simpa [sx, sy, cpx, cpy, r, hr] using hsnd
    have hrIn : HLHDAInwardDir r.dir := hlhda_cutState_inward hx hxne
    have hsxLegal : ∀ t ∈ sx, t = 1 ∨ t = -1 := by
      intro t ht
      exact hx.1 t (List.mem_of_mem_drop ht)
    have hsyLegal : ∀ t ∈ sy, t = 1 ∨ t = -1 := by
      intro t ht
      exact hy.1 t (List.mem_of_mem_drop ht)
    have hsxDir : ∀ t us, sx = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor ∨
          HLHDAInwardDir (hlha_negCoord (r.dir.turn t)) := by
      intro t us hs
      by_cases hflat : hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor
      · exact Or.inl hflat
      · exact Or.inr (hlhda_suffix_side_hypotheses hx
          (by simpa [sx, cpx] using hs) hflat).1
    have hsyDir : ∀ t us, sy = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor ∨
          HLHDAInwardDir (hlha_negCoord (r.dir.turn t)) := by
      intro t us hs
      by_cases hflat : hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor
      · exact Or.inl hflat
      · have hh := hlhda_suffix_side_hypotheses hy
            (by simpa [sy, cpy] using hs) (by simpa [hr] using hflat)
        simpa [hr] using Or.inr hh.1
    have hsxFlat : ∀ t us, sx = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor → us = [] := by
      intro t us hs hflat
      apply hlhda_suffix_flat_forces_terminal hx hxne
        (by simpa [sx, cpx] using hs)
      rw [← hflat]
      exact hlhda_firstDir_mem_edgeVertices _ us
    have hsyFlat : ∀ t us, sy = t :: us →
        hlha_negCoord (r.dir.turn t) = hlhda_flatNeighbor → us = [] := by
      intro t us hs hflat
      apply hlhda_suffix_flat_forces_terminal hy hyne
        (by simpa [sy, cpy] using hs)
      rw [← hflat, hr]
      exact hlhda_firstDir_mem_edgeVertices _ us
    have hsuf : sx = sy := hlhda_forwardCode_injective r.dir hrIn
      hsxLegal hsyLegal hsxDir hsyDir hsxFlat hsyFlat hsufCode
    calc
      xs = px ++ sx := by
        simpa [px, sx, cpx] using (List.take_append_drop cpx xs).symm
      _ = py ++ sy := congrArg₂ List.append hpre hsuf
      _ = ys := by
        simpa [py, sy, cpy] using List.take_append_drop cpy ys


end
end StatMech.Universality
