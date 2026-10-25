/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part3


namespace StatMech.Universality

open HexWalk


@[simp] theorem hlha_outerStep_eq : hlha_outerStep = ⟨0, -1⟩ := by
  simp [hlha_outerStep, HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.right]

@[simp] theorem hlha_coordHeight_zero :
    HexReturnCoord.zero.x - HexReturnCoord.zero.y = 0 := rfl

@[simp] theorem hlha_outerStep_height :
    hlha_outerStep.x - hlha_outerStep.y = 1 := by
  rw [hlha_outerStep_eq]
  rfl

theorem hlha_normCoord_height (d p : HexReturnCoord) :
    (hlha_normCoord d p).x - (hlha_normCoord d p).y =
      -(p.x - p.y) := by
  unfold hlha_normCoord
  split <;> simp <;> omega

theorem hlha_normCoord_injective (d : HexReturnCoord) :
    Function.Injective (hlha_normCoord d) := by
  unfold hlha_normCoord
  split
  · exact hlha_swapCoord_injective
  · exact hlha_negCoord_injective

theorem hlha_normDir_eq (d : HexReturnCoord) (hd : HLHAAwayDir d) :
    hlha_normCoord d d =
      hlha_outerStep.turn (hlha_cutTurn d) := by
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [hlha_normCoord, hlha_useSwap, hlha_cutTurn, hlha_outerStep,
      HexReturnCoord.base, HexReturnCoord.turn, HexReturnCoord.left,
      HexReturnCoord.right, hlha_swapCoord, hlha_negCoord]

theorem hlha_normTurns_legal (d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∀ t ∈ hlha_normTurns d ts, t = 1 ∨ t = -1 := by
  unfold hlha_normTurns
  split
  · intro t ht
    unfold hsc_negTurns at ht
    rw [List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    rcases hlegal u hu with rfl | rfl <;> simp
  · exact hlegal

theorem hlha_augmentSide_legal (d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∀ t ∈ hlha_augmentSide d ts, t = 1 ∨ t = -1 := by
  intro t ht
  simp only [hlha_augmentSide, List.mem_cons] at ht
  rcases ht with rfl | rfl | ht
  · exact Or.inr rfl
  · unfold hlha_cutTurn
    split <;> simp
  · exact hlha_normTurns_legal d ts hlegal t ht

@[simp] theorem hlha_augmentSide_length (d : HexReturnCoord)
    (ts : List ℤ) :
    (hlha_augmentSide d ts).length = ts.length + 2 := by
  unfold hlha_augmentSide hlha_normTurns
  split <;> simp [hsc_negTurns]

theorem hlha_normEdgeVertices (d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_edgeVertices hlha_outerStep (hlha_normCoord d d)
        (hlha_normTurns d ts) =
      (hlha_edgeVertices HexReturnCoord.zero d ts).map
        (fun p => hlha_outerStep.add (hlha_normCoord d p)) := by
  unfold hlha_normTurns hlha_normCoord
  split <;> rename_i hswap
  · have htrans := hlha_edgeVertices_translate hlha_outerStep
        HexReturnCoord.zero (hlha_swapCoord d) (hsc_negTurns ts)
    have hswapv := hlha_edgeVertices_swap HexReturnCoord.zero d ts hlegal
    simp only [hlha_add_zero, hlha_swapCoord_zero] at htrans hswapv
    rw [htrans, hswapv, List.map_map]
    rfl
  · have htrans := hlha_edgeVertices_translate hlha_outerStep
        HexReturnCoord.zero (hlha_negCoord d) ts
    have hnegv := hlha_edgeVertices_neg HexReturnCoord.zero d ts hlegal
    simp only [hlha_add_zero, hlha_negCoord_zero] at htrans hnegv
    rw [htrans, hnegv, List.map_map]
    rfl

theorem hlha_coordVertices_augmentSide (d : HexReturnCoord) (ts : List ℤ)
    (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (hlha_augmentSide d ts) =
      HexReturnCoord.zero ::
        (hlha_edgeVertices HexReturnCoord.zero d ts).map
          (fun p => hlha_outerStep.add (hlha_normCoord d p)) := by
  rw [show hlha_augmentSide d ts =
      (-1 : ℤ) :: hlha_cutTurn d :: hlha_normTurns d ts from rfl]
  rw [hlha_coordVertices_cons_eq_edge]
  simp only [hlha_edgeVertices]
  change HexReturnCoord.zero ::
      hlha_edgeVertices hlha_outerStep
        (hlha_outerStep.turn (hlha_cutTurn d)) (hlha_normTurns d ts) = _
  rw [← hlha_normDir_eq d hd, hlha_normEdgeVertices d ts hlegal]


theorem hlha_augmented_vertex_height_pos (d p : HexReturnCoord)
    (hp : p.x - p.y ≤ 0) :
    0 < (hlha_outerStep.add (hlha_normCoord d p)).x -
      (hlha_outerStep.add (hlha_normCoord d p)).y := by
  have ho := hlha_outerStep_height
  have hn := hlha_normCoord_height d p
  simp only [HexReturnCoord.add]
  omega


theorem hlha_coordVertices_augmentSide_nodup (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d ts).Nodup)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
      (hlha_augmentSide d ts)).Nodup := by
  rw [hlha_coordVertices_augmentSide d ts hd hlegal]
  rw [List.nodup_cons]
  constructor
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, hp, heq⟩ := hmem
    have hpos := hlha_augmented_vertex_height_pos d p (hbehind p hp)
    rw [heq] at hpos
    simp [HexReturnCoord.zero] at hpos
  · apply hnodup.map
    intro p q heq
    apply hlha_normCoord_injective d
    exact hlha_add_left_injective hlha_outerStep heq


end StatMech.Universality
