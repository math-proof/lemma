/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part2


namespace StatMech.Universality

open HexWalk


@[simp] theorem hlha_coordVertices_length (p d : HexReturnCoord)
    (ts : List ℤ) :
    (hlha_coordVertices p d ts).length = ts.length + 1 := by
  induction ts generalizing p d with
  | nil => rfl
  | cons t ts ih => simp [hlha_coordVertices, ih]

@[simp] theorem hlha_edgeVertices_length (p d : HexReturnCoord)
    (ts : List ℤ) :
    (hlha_edgeVertices p d ts).length = ts.length + 2 := by
  induction ts generalizing p d with
  | nil => rfl
  | cons t ts ih => simp [hlha_edgeVertices, ih]

theorem hlha_edgeVertices_start_mem (p d : HexReturnCoord) (ts : List ℤ) :
    p ∈ hlha_edgeVertices p d ts := by
  cases ts <;> simp [hlha_edgeVertices]

theorem hlha_coordVertices_cons_eq_edge (p d : HexReturnCoord)
    (t : ℤ) (ts : List ℤ) :
    hlha_coordVertices p d (t :: ts) =
      hlha_edgeVertices p (d.turn t) ts := by
  induction ts generalizing p d t with
  | nil => simp [hlha_coordVertices, hlha_edgeVertices]
  | cons u ts ih =>
      rw [hlha_coordVertices, hlha_edgeVertices, ih]

theorem hlha_coordVertices_neg (p d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_coordVertices (hlha_negCoord p) (hlha_negCoord d) ts =
      (hlha_coordVertices p d ts).map hlha_negCoord := by
  induction ts generalizing p d with
  | nil => simp [hlha_coordVertices]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simp only [hlha_coordVertices, List.map_cons]
      rw [← hlha_negCoord_turn d ht, ← hlha_negCoord_add]
      exact congrArg (List.cons (hlha_negCoord p))
        (ih (p.add (d.turn t)) (d.turn t) htail)

theorem hlha_edgeVertices_neg (p d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_edgeVertices (hlha_negCoord p) (hlha_negCoord d) ts =
      (hlha_edgeVertices p d ts).map hlha_negCoord := by
  induction ts generalizing p d with
  | nil => simp [hlha_edgeVertices]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simp only [hlha_edgeVertices, List.map_cons]
      rw [← hlha_negCoord_add, ← hlha_negCoord_turn d ht]
      exact congrArg (List.cons (hlha_negCoord p))
        (ih (p.add d) (d.turn t) htail)

theorem hlha_edgeVertices_swap (p d : HexReturnCoord) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hlha_edgeVertices (hlha_swapCoord p) (hlha_swapCoord d)
        (hsc_negTurns ts) =
      (hlha_edgeVertices p d ts).map hlha_swapCoord := by
  induction ts generalizing p d with
  | nil => simp [hlha_edgeVertices]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      rw [hsc_negTurns_cons]
      simp only [hlha_edgeVertices, List.map_cons]
      rw [← hlha_swapCoord_add, ← hlha_swapCoord_turn d ht]
      exact congrArg (List.cons (hlha_swapCoord p))
        (ih (p.add d) (d.turn t) htail)

theorem hlha_edgeVertices_translate (q p d : HexReturnCoord)
    (ts : List ℤ) :
    hlha_edgeVertices (q.add p) d ts =
      (hlha_edgeVertices p d ts).map (fun r => q.add r) := by
  induction ts generalizing p d with
  | nil =>
      simp [hlha_edgeVertices, HexReturnCoord.add]
      cases q
      cases p
      cases d
      simp
      constructor <;> omega
  | cons t ts ih =>
      simp only [hlha_edgeVertices, List.map_cons]
      rw [show (q.add p).add d = q.add (p.add d) by
        cases q
        cases p
        cases d
        simp [HexReturnCoord.add]
        constructor <;> omega]
      exact congrArg (List.cons (q.add p)) (ih (p.add d) (d.turn t))


end StatMech.Universality
