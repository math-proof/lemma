/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hexW2S_verticesAux_translate (c m : ℂ) (h : ℤ) (ts : List ℤ) :
    HexWalk.verticesAux (m + c) h ts = (HexWalk.verticesAux m h ts).map (· + c) := by
  induction ts generalizing m h with
  | nil =>
    rw [HexWalk.verticesAux_nil, HexWalk.verticesAux_nil, List.map_singleton]
    ring_nf
  | cons t ts ih =>
    rw [HexWalk.verticesAux_cons, HexWalk.verticesAux_cons, List.map_cons]
    congr 1
    · ring
    · rw [show m + c + HexWalk.halfStep h + HexWalk.halfStep (h + t)
          = (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) + c by ring]
      exact ih _ _


theorem hexW2S_isSAW_translate (c m : ℂ) (h : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns (m + c) h ts).IsSAW ↔ (HexWalk.ofTurns m h ts).IsSAW := by
  unfold HexWalk.IsSAW HexWalk.vertices HexWalk.ofTurns
  simp only
  rw [hexW2S_verticesAux_translate, List.nodup_map_iff (add_left_injective c)]


theorem hexW2S_isLegalSAW_translate (c m : ℂ) (h : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns (m + c) h ts).IsLegalSAW ↔ (HexWalk.ofTurns m h ts).IsLegalSAW := by
  unfold HexWalk.IsLegalSAW HexWalk.LegalTurns HexWalk.ofTurns
  simp only
  rw [show (HexWalk.mk (m + c) h ts).IsSAW ↔ (HexWalk.mk m h ts).IsSAW from
    hexW2S_isSAW_translate c m h ts]


theorem hexW2S_hexSAWwt_translate (c m : ℂ) (h : ℤ) (x : ℝ) (ts : List ℤ) :
    hexSAWwt (m + c) h x ts = hexSAWwt m h x ts := by
  unfold hexSAWwt
  have hiff := hexW2S_isLegalSAW_translate c m h ts
  by_cases hl : (HexWalk.ofTurns m h ts).IsLegalSAW
  · rw [if_pos (hiff.mpr hl), if_pos hl]
    rfl
  · rw [if_neg (fun hh => hl (hiff.mp hh)), if_neg hl]


theorem hexW2S_hexSAWwt_mid_indep (m m' : ℂ) (h : ℤ) (x : ℝ) (ts : List ℤ) :
    hexSAWwt m' h x ts = hexSAWwt m h x ts := by
  have := hexW2S_hexSAWwt_translate (m' - m) m h x ts
  rwa [add_sub_cancel] at this


theorem hexW2S_hexSAWwt_mono_fugacity (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 ≤ x)
    (hxχ : x ≤ χ) (ts : List ℤ) :
    hexSAWwt a h0 x ts ≤ hexSAWwt a h0 χ ts := by
  unfold hexSAWwt
  split
  · exact pow_le_pow_left₀ hx hxχ _
  · exact le_refl _


theorem hexW2S_diff_summable (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ)
    (memD : List ℤ → Prop)
    (hDcrit : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 χ d.1)) :
    Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1) :=
  hDcrit.of_nonneg_of_le (fun d => hexSAWwt_nonneg a h0 hx d.1)
    (fun d => hexW2S_hexSAWwt_mono_fugacity a h0 hx hxχ d.1)


theorem hexW2S_trivialHalf_wt (mid : ℂ) (h0 : ℤ) (x : ℝ) :
    hexW2_halfWt x ⟨mid, h0, []⟩ = x := by
  change hexSAWwt mid h0 x [] = x
  rw [hexSAWwt_of_isLegalSAW mid h0 x (HexWalk.trivialWalk_isLegalSAW mid h0)]
  rw [show (HexWalk.ofTurns mid h0 []).numVertices = 1 from rfl, pow_one]


theorem hexW2S_halfWt_not_summable {x : ℝ} (hx : 0 < x) :
    ¬ Summable (hexW2_halfWt x) := by
  intro hsum
  have hc : (Function.support (hexW2_halfWt x)).Countable := hsum.countable_support
  
  set g : ℝ → HexW2Half := fun t => ⟨(t : ℂ), 0, []⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have : ((a : ℂ)) = ((b : ℂ)) := (HexW2Half.mk.injEq ..).mp hab |>.1
    exact Complex.ofReal_injective this
  have hsub : Set.range g ⊆ Function.support (hexW2_halfWt x) := by
    rintro _ ⟨t, rfl⟩
    change hexW2_halfWt x ⟨(t : ℂ), 0, []⟩ ≠ 0
    rw [hexW2S_trivialHalf_wt]; exact ne_of_gt hx
  have hrangeC : (Set.range g).Countable := hc.mono hsub
  haveI : Countable (Set.range g) := hrangeC.to_subtype
  have : Countable ℝ :=
    Function.Injective.countable (f := Set.rangeFactorization g)
      (fun a b hab => hginj (congrArg Subtype.val hab))
  exact not_countable this


end StatMech.Universality
