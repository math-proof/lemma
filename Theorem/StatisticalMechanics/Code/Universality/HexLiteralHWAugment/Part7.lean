/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part7


namespace StatMech.Universality

open HexWalk


theorem hlha_suffix_side_hypotheses (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hsource : (ofTurns a h0 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuffix : ts.drop (hexW2_cutPos 0 ts) = t :: us) :
    let d := (hlha_cutState ts).dir.turn t
    HLHAAwayDir d ∧
      (∀ u ∈ us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d us).Nodup ∧
      ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d us,
        p.x - p.y ≤ 0 := by
  have hstd := hlha_source_standard_legal a h0 ts hsource
  have hcple := hexW2_cutPos_le 0 ts
  let r := hlha_cutState ts
  let d := r.dir.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_drop
    rw [hsuffix]
    simp
  have ht := hstd.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hudrop : u ∈ ts.drop (hexW2_cutPos 0 ts) := by
      rw [hsuffix]
      simp [hu]
    exact hstd.1 u (List.mem_of_mem_drop hudrop)
  have habs :
      hlha_edgeVertices r.pos d us =
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).drop
          (hexW2_cutPos 0 ts) := by
    have hdrop := hlha_coordVertices_drop HexReturnCoord.zero
      HexReturnCoord.base ts (hexW2_cutPos 0 ts) hcple
    rw [hsuffix] at hdrop
    change hlha_coordVertices r.pos r.dir (t :: us) = _ at hdrop
    rw [hlha_coordVertices_cons_eq_edge] at hdrop
    exact hdrop
  have htrans :
      hlha_edgeVertices r.pos d us =
        (hlha_edgeVertices HexReturnCoord.zero d us).map r.pos.add := by
    simpa [hlha_add_zero] using
      hlha_edgeVertices_translate r.pos HexReturnCoord.zero d us
  have hfullnd := hlha_source_coord_nodup a h0 ts hsource
  have habsnd : (hlha_edgeVertices r.pos d us).Nodup := by
    rw [habs]
    exact hfullnd.drop
  have hrelnd : (hlha_edgeVertices HexReturnCoord.zero d us).Nodup := by
    rw [htrans] at habsnd
    exact habsnd.of_map
  have hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d us,
      p.x - p.y ≤ 0 := by
    intro p hp
    have habsmem : r.pos.add p ∈ hlha_edgeVertices r.pos d us := by
      rw [htrans, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hdropmem : r.pos.add p ∈
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).drop
          (hexW2_cutPos 0 ts) := by
      rw [← habs]
      exact habsmem
    have hfullmem : r.pos.add p ∈
        hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts :=
      List.mem_of_mem_drop hdropmem
    obtain ⟨k, hk, heq⟩ := hlha_mem_coordVertices
      HexReturnCoord.zero HexReturnCoord.base ts hfullmem
    have hmax := hlha_cut_latticeHeight_max ts hstd.1 k hk
    have hrheight : r.pos.x - r.pos.y =
        hlhr_latticeHeight ts (hexW2_cutPos 0 ts) := by
      rfl
    have hpheight : (r.pos.add p).x - (r.pos.add p).y =
        hlhr_latticeHeight ts k := by
      rw [heq]
      rfl
    simp only [HexReturnCoord.add] at hpheight
    omega
  have hrunit : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base (ts.take (hexW2_cutPos 0 ts))
      HexReturnCoord.base_isUnit
    intro u hu
    exact hstd.1 u (List.mem_of_mem_take hu)
  have hdunit : d.IsUnit := r.dir.isUnit_turn hrunit ht
  have hdmem : d ∈ hlha_edgeVertices HexReturnCoord.zero d us := by
    cases us with
    | nil => simp [hlha_edgeVertices]
    | cons u us =>
        simp only [hlha_edgeVertices, List.mem_cons]
        right
        simpa using hlha_edgeVertices_start_mem d (d.turn u) us
  have hdheight := hbehind d hdmem
  exact ⟨hlha_awayDir_of_isUnit_of_height_nonpos d hdunit hdheight,
    hus, hrelnd, hbehind⟩


theorem hlha_suffixAugment_spec (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns 0 0 (hlha_suffixAugment ts)).IsLegalSAW ∧
      HLHRLiteralHalfSpace 0 (hlha_suffixAugment ts) ∧
      (hlha_suffixAugment ts).length =
        (ts.drop (hexW2_cutPos 0 ts)).length + 1 := by
  unfold hlha_suffixAugment
  generalize hs : ts.drop (hexW2_cutPos 0 ts) = suffix
  cases suffix with
  | nil =>
      simp only
      refine ⟨hlha_emptyAugment_isLegalSAW,
        hlha_emptyAugment_halfSpace, ?_⟩
      simp [hlha_emptyAugment]
  | cons t us =>
      obtain ⟨hd, hlegal, hnodup, hbehind⟩ :=
        hlha_suffix_side_hypotheses a h0 ts hsource hs
      refine ⟨hlha_augmentSide_isLegalSAW _ _ hd hlegal hnodup hbehind,
        hlha_augmentSide_halfSpace _ _ hd hlegal hbehind, ?_⟩
      rw [hlha_augmentSide_length]
      simp


@[simp] theorem hlha_negCoord_negCoord (p : HexReturnCoord) :
    hlha_negCoord (hlha_negCoord p) = p := by
  cases p
  simp [hlha_negCoord]

@[simp] theorem hlha_add_neg_self (p : HexReturnCoord) :
    p.add (hlha_negCoord p) = HexReturnCoord.zero := by
  cases p
  simp [HexReturnCoord.add, HexReturnCoord.zero, hlha_negCoord]

@[simp] theorem hlha_add_neg_cancel_left (p q : HexReturnCoord) :
    (p.add q).add (hlha_negCoord q) = p := by
  cases p
  cases q
  simp [HexReturnCoord.add, hlha_negCoord]

theorem hlha_negTurn_back (d : HexReturnCoord) {t : ℤ}
    (ht : t = 1 ∨ t = -1) :
    (hlha_negCoord (d.turn t)).turn (-t) = hlha_negCoord d := by
  rcases d with ⟨x, y⟩
  rcases ht with rfl | rfl <;>
    simp [hlha_negCoord, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] <;> omega

@[simp] theorem hlha_loopReverse_cons (t : ℤ) (ts : List ℤ) :
    loopReverse (t :: ts) = loopReverse ts ++ [-t] := by
  simp [loopReverse]

theorem hlha_coordRun_append (p d : HexReturnCoord) (xs ys : List ℤ) :
    hlhr_coordRun p d (xs ++ ys) =
      let r := hlhr_coordRun p d xs
      hlhr_coordRun r.pos r.dir ys := by
  induction xs generalizing p d with
  | nil => simp [hlhr_coordRun]
  | cons t xs ih =>
      simp only [List.cons_append, hlhr_coordRun]
      exact ih (p.add (d.turn t)) (d.turn t)


theorem hlha_edgeVertices_append_single (p d : HexReturnCoord)
    (ts : List ℤ) (t : ℤ) :
    let r := hlhr_coordRun (p.add d) d ts
    hlha_edgeVertices p d (ts ++ [t]) =
      hlha_edgeVertices p d ts ++ [r.pos.add (r.dir.turn t)] := by
  induction ts generalizing p d with
  | nil =>
      simp [hlha_edgeVertices, hlhr_coordRun]
  | cons u ts ih =>
      simp only [List.cons_append, hlha_edgeVertices, hlhr_coordRun,
        List.cons_append]
      rw [ih (p.add d) (d.turn u)]


theorem hlha_edgeVertices_loopReverse (p d : HexReturnCoord)
    (ts : List ℤ) (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hlhr_coordRun (p.add d) d ts
    hlha_edgeVertices r.pos (hlha_negCoord r.dir) (loopReverse ts) =
        (hlha_edgeVertices p d ts).reverse ∧
      hlhr_coordRun (r.pos.add (hlha_negCoord r.dir))
          (hlha_negCoord r.dir) (loopReverse ts) =
        ⟨p, hlha_negCoord d⟩ := by
  induction ts generalizing p d with
  | nil =>
      simp [hlhr_coordRun, hlha_edgeVertices, loopReverse]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      let r := hlhr_coordRun ((p.add d).add e) e ts
      have hih := ih (p.add d) e htail
      change
        hlha_edgeVertices r.pos (hlha_negCoord r.dir)
            (loopReverse (t :: ts)) =
            (hlha_edgeVertices p d (t :: ts)).reverse ∧
          hlhr_coordRun (r.pos.add (hlha_negCoord r.dir))
              (hlha_negCoord r.dir) (loopReverse (t :: ts)) =
            ⟨p, hlha_negCoord d⟩
      rw [hlha_loopReverse_cons]
      constructor
      · rw [hlha_edgeVertices_append_single]
        rw [hih.1]
        simp only [hlha_edgeVertices, List.reverse_cons]
        rw [hih.2]
        simp only
        rw [hlha_negTurn_back d ht, hlha_add_neg_cancel_left]
      · rw [hlha_coordRun_append]
        rw [hih.2]
        simp only [hlhr_coordRun]
        rw [hlha_negTurn_back d ht, hlha_add_neg_cancel_left]


end StatMech.Universality
