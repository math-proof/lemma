/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part4


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhda_augmentSide_length (d : HexReturnCoord)
    (internal : List ℤ) :
    (hlhda_augmentSide d internal).length = internal.length + 3 := by
  simp [hlhda_augmentSide]

@[simp] theorem hlhda_emptySide_length : hlhda_emptySide.length = 2 := rfl

theorem hlhda_augmentSide_legal (d : HexReturnCoord) (internal : List ℤ)
    (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1) :
    (ofTurns hexAWStart 1 (hlhda_augmentSide d internal)).LegalTurns := by
  intro t ht
  change t ∈ (-1 : ℤ) :: 1 :: hlhda_entryTurn d :: internal at ht
  simp only [List.mem_cons] at ht
  rcases ht with rfl | rfl | rfl | ht
  · simp
  · simp
  · exact hlhda_entryTurn_legal d
  · exact hlegal t ht

theorem hlhda_emptySide_legal :
    (ofTurns hexAWStart 1 hlhda_emptySide).LegalTurns := by
  intro t ht
  simp [hlhda_emptySide] at ht
  rcases ht with rfl | rfl <;> simp

theorem hlhda_coordVertices_augmentSide (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d) :
    hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (hlhda_augmentSide d internal) =
      HexReturnCoord.zero :: hlhda_spacerWhite ::
        (hlha_edgeVertices HexReturnCoord.zero d internal).map
          hlhda_spacerRoot.add := by
  rw [show hlhda_augmentSide d internal =
      (-1 : ℤ) :: 1 :: hlhda_entryTurn d :: internal by
    simp [hlhda_augmentSide]]
  simp only [hlha_coordVertices]
  change HexReturnCoord.zero :: hlhda_spacerWhite ::
      hlha_coordVertices hlhda_spacerRoot HexReturnCoord.base
          (hlhda_entryTurn d :: internal) = _
  rw [hlha_coordVertices_cons_eq_edge, hlhda_entryTurn_dir hd]
  have htrans := hlha_edgeVertices_translate hlhda_spacerRoot
    HexReturnCoord.zero d internal
  simpa [hlhda_spacerRoot] using htrans

theorem hlhda_coordVertices_emptySide :
    hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        hlhda_emptySide =
      [HexReturnCoord.zero, hlhda_spacerWhite, hlhda_spacerRoot] := by
  simp [hlhda_emptySide, hlha_coordVertices, hlhda_spacerWhite,
    hlhda_spacerRoot, HexReturnCoord.zero, HexReturnCoord.base,
    HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.right,
    HexReturnCoord.add]

@[simp] theorem hlhda_score_zero :
    hlhda_score HexReturnCoord.zero = 0 := rfl

@[simp] theorem hlhda_score_spacerWhite :
    hlhda_score hlhda_spacerWhite = 1 := rfl

@[simp] theorem hlhda_score_spacerRoot :
    hlhda_score hlhda_spacerRoot = 3 := rfl

theorem hlhda_score_add (p q : HexReturnCoord) :
    hlhda_score (p.add q) = hlhda_score p + hlhda_score q := by
  cases p
  cases q
  simp [hlhda_score, HexReturnCoord.add]
  ring

theorem hlhda_spacerRoot_add_ne_zero (p : HexReturnCoord)
    (hp : -2 ≤ hlhda_score p) :
    hlhda_spacerRoot.add p ≠ HexReturnCoord.zero := by
  intro heq
  have hs := congrArg hlhda_score heq
  rw [hlhda_score_add] at hs
  simp at hs
  omega

theorem hlhda_spacerRoot_add_eq_white_iff (p : HexReturnCoord) :
    hlhda_spacerRoot.add p = hlhda_spacerWhite ↔
      p = hlhda_flatNeighbor := by
  rcases p with ⟨x, y⟩
  simp [hlhda_spacerRoot, hlhda_spacerWhite, hlhda_flatNeighbor,
    HexReturnCoord.add, HexReturnCoord.mk.injEq] <;> omega

theorem hlhda_coordVertices_augmentSide_nodup (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    (hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d internal) :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
      (hlhda_augmentSide d internal)).Nodup := by
  rw [hlhda_coordVertices_augmentSide d internal hd]
  simp only [List.nodup_cons]
  constructor
  · simp only [List.mem_cons, List.mem_map, not_or]
    constructor
    · decide
    · rintro ⟨p, hp, heq⟩
      exact hlhda_spacerRoot_add_ne_zero p (hscore p hp) heq
  · constructor
    · simp only [List.mem_map]
      rintro ⟨p, hp, heq⟩
      have hpflat := (hlhda_spacerRoot_add_eq_white_iff p).mp heq
      exact hflat (hpflat ▸ hp)
    · exact hnodup.map (hlha_add_left_injective hlhda_spacerRoot)

theorem hlhda_coordVertices_emptySide_nodup :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
      hlhda_emptySide).Nodup := by
  rw [hlhda_coordVertices_emptySide]
  decide

theorem hlhda_augmentSide_isLegalSAW (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    (hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d internal) :
    (ofTurns hexAWStart 1 (hlhda_augmentSide d internal)).IsLegalSAW := by
  have hturns := hlhda_augmentSide_legal d internal hlegal
  refine ⟨hturns, ?_⟩
  have hstdTurns : (ofTurns 0 0 (hlhda_augmentSide d internal)).LegalTurns :=
    hturns
  have hstdSaw : (ofTurns 0 0 (hlhda_augmentSide d internal)).IsSAW := by
    rw [hlha_standard_isSAW_iff _ hstdTurns]
    exact hlhda_coordVertices_augmentSide_nodup d internal hd hnodup
      hscore hflat
  exact (hhe_isSAW_rebase 0 hexAWStart 0 1
    (hlhda_augmentSide d internal)).mpr hstdSaw

theorem hlhda_emptySide_isLegalSAW :
    (ofTurns hexAWStart 1 hlhda_emptySide).IsLegalSAW := by
  refine ⟨hlhda_emptySide_legal, ?_⟩
  have hstdTurns : (ofTurns 0 0 hlhda_emptySide).LegalTurns :=
    hlhda_emptySide_legal
  have hstdSaw : (ofTurns 0 0 hlhda_emptySide).IsSAW := by
    rw [hlha_standard_isSAW_iff _ hstdTurns]
    exact hlhda_coordVertices_emptySide_nodup
  exact (hhe_isSAW_rebase 0 hexAWStart 0 1 hlhda_emptySide).mpr hstdSaw

theorem hlhda_augmentSide_runnerScore_pos (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    {k : ℕ} (hk : 0 < k)
    (hkle : k ≤ (hlhda_augmentSide d internal).length) :
    0 < hlhda_score
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        ((hlhda_augmentSide d internal).take k)).pos := by
  have hmem := hlha_coordRun_take_mem_tail HexReturnCoord.zero
    HexReturnCoord.base (hlhda_augmentSide d internal) hk hkle
  rw [hlhda_coordVertices_augmentSide d internal hd] at hmem
  simp only [List.tail_cons, List.mem_cons, List.mem_map] at hmem
  rcases hmem with heq | ⟨p, hp, heq⟩
  · rw [heq]
    simp
  · rw [← heq, hlhda_score_add]
    simp
    have hpScore := hscore p hp
    omega

theorem hlhda_emptySide_runnerScore_pos {k : ℕ} (hk : 0 < k)
    (hkle : k ≤ hlhda_emptySide.length) :
    0 < hlhda_score
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (hlhda_emptySide.take k)).pos := by
  have hmem := hlha_coordRun_take_mem_tail HexReturnCoord.zero
    HexReturnCoord.base hlhda_emptySide hk hkle
  rw [hlhda_coordVertices_emptySide] at hmem
  simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with heq | heq <;> rw [heq] <;> simp

theorem hlhda_augmentSide_halfSpace (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
    (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal,
      -2 ≤ hlhda_score p)
    (hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d internal) :
    HLHDLiteralHalfSpace (hlhda_augmentSide d internal)
      (hlhda_augmentSide_isLegalSAW d internal hd hlegal hnodup hscore hflat) := by
  let hleg := hlhda_augmentSide_isLegalSAW d internal hd hlegal hnodup
    hscore hflat
  intro k hk hkle
  have hs := hlhda_augmentSide_runnerScore_pos d internal hd hscore hk hkle
  have hr := hlhda_prefixCoord_returnPos
    (hlhda_augmentSide d internal) hleg k
  rw [hr] at hs
  have hdepth := hlhda_depth_pos_of_returnScore_pos _ hs
  change (hlhd_depth (hlhda_augmentSide d internal) hleg 0 : ℝ) <
    hlhd_depth (hlhda_augmentSide d internal) hleg k
  rw [hlhda_depth_zero]
  exact_mod_cast hdepth

theorem hlhda_emptySide_halfSpace :
    HLHDLiteralHalfSpace hlhda_emptySide hlhda_emptySide_isLegalSAW := by
  intro k hk hkle
  have hs := hlhda_emptySide_runnerScore_pos hk hkle
  have hr := hlhda_prefixCoord_returnPos hlhda_emptySide
    hlhda_emptySide_isLegalSAW k
  rw [hr] at hs
  have hdepth := hlhda_depth_pos_of_returnScore_pos _ hs
  change (hlhd_depth hlhda_emptySide hlhda_emptySide_isLegalSAW 0 : ℝ) <
    hlhd_depth hlhda_emptySide hlhda_emptySide_isLegalSAW k
  rw [hlhda_depth_zero]
  exact_mod_cast hdepth


end
end StatMech.Universality
