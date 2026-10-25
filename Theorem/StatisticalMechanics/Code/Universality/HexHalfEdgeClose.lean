/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4
import Def.StatisticalMechanics.Code.Universality.HexHalfEdgeClose


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hhe_rho_norm (h h' : ℤ) : ‖hhe_rho h h'‖ = 1 := by
  unfold hhe_rho
  rw [norm_mul, norm_inv, norm_hexUnit, norm_hexUnit]; norm_num


theorem hhe_rho_ne_zero (h h' : ℤ) : hhe_rho h h' ≠ 0 := by
  intro hz; have := hhe_rho_norm h h'; rw [hz] at this; simp at this


theorem hhe_hexUnit_add (k s : ℤ) :
    hexUnit (k + s) = hexUnit k * Complex.exp (Complex.I * ((s : ℝ) * (Real.pi / 3))) := by
  unfold hexUnit
  rw [← Complex.exp_add]; congr 1; push_cast; ring


theorem hhe_halfStep_shift (h h' : ℤ) (s : ℤ) :
    halfStep (h' + s) = hhe_rho h h' * halfStep (h + s) := by
  unfold halfStep hhe_rho
  rw [hhe_hexUnit_add h' s, hhe_hexUnit_add h s]
  have hh : hexUnit h ≠ 0 := hexUnit_ne_zero h
  field_simp


theorem hhe_verticesAux_rigid (h h' : ℤ) (ts : List ℤ) :
    ∀ (m m' : ℂ) (s : ℤ),
      verticesAux m' (h' + s) ts
        = (verticesAux m (h + s) ts).map (fun z => hhe_rho h h' * (z - m) + m') := by
  induction ts with
  | nil =>
    intro m m' s
    simp only [verticesAux_nil, List.map_cons, List.map_nil]
    congr 1
    rw [hhe_halfStep_shift h h' s]; ring
  | cons t ts ih =>
    intro m m' s
    rw [verticesAux_cons, verticesAux_cons, List.map_cons]
    congr 1
    · rw [hhe_halfStep_shift h h' s]; ring
    · have key := ih (m + halfStep (h + s) + halfStep (h + s + t))
        (m' + halfStep (h' + s) + halfStep (h' + s + t)) (s + t)
      rw [show h' + (s + t) = h' + s + t by ring, show h + (s + t) = h + s + t by ring] at key
      rw [key]
      apply List.map_congr_left
      intro z _
      rw [hhe_halfStep_shift h h' s,
          show h' + s + t = h' + (s + t) by ring, hhe_halfStep_shift h h' (s + t),
          show h + (s + t) = h + s + t by ring]
      ring


theorem hhe_verticesAux_rigid0 (h h' : ℤ) (ts : List ℤ) (m m' : ℂ) :
    verticesAux m' h' ts
      = (verticesAux m h ts).map (fun z => hhe_rho h h' * (z - m) + m') := by
  have := hhe_verticesAux_rigid h h' ts m m' 0
  simpa using this


theorem hhe_nodup_iff (h h' : ℤ) (ts : List ℤ) (m m' : ℂ) :
    (verticesAux m' h' ts).Nodup ↔ (verticesAux m h ts).Nodup := by
  rw [hhe_verticesAux_rigid0 h h' ts m m']
  have hrne := hhe_rho_ne_zero h h'
  have hinj : Function.Injective (fun z : ℂ => hhe_rho h h' * (z - m) + m') := by
    intro a b hab
    simp only at hab
    have h2 : hhe_rho h h' * (a - m) = hhe_rho h h' * (b - m) := by linear_combination hab
    have := mul_left_cancel₀ hrne h2
    linear_combination this
  exact List.nodup_map_iff hinj


theorem hhe_isSAW_rebase (m m' : ℂ) (h h' : ℤ) (ts : List ℤ) :
    (ofTurns m' h' ts).IsSAW ↔ (ofTurns m h ts).IsSAW := by
  unfold IsSAW vertices ofTurns
  simp only
  exact hhe_nodup_iff h h' ts m m'


theorem hhe_legalTurns_rebase (m m' : ℂ) (h h' : ℤ) (ts : List ℤ) :
    (ofTurns m' h' ts).LegalTurns ↔ (ofTurns m h ts).LegalTurns := by
  unfold LegalTurns
  simp only [ofTurns_turns]


theorem hhe_isLegalSAW_rebase (m m' : ℂ) (h h' : ℤ) (ts : List ℤ) :
    (ofTurns m' h' ts).IsLegalSAW ↔ (ofTurns m h ts).IsLegalSAW := by
  unfold IsLegalSAW
  rw [hhe_legalTurns_rebase m m' h h' ts, hhe_isSAW_rebase m m' h h' ts]


theorem hhe_hexSAWwt_rebase (m m' : ℂ) (h h' : ℤ) (x : ℝ) (ts : List ℤ) :
    hexSAWwt m' h' x ts = hexSAWwt m h x ts := by
  unfold hexSAWwt
  by_cases hl : (HexWalk.ofTurns m h ts).IsLegalSAW
  · rw [if_pos hl, if_pos ((hhe_isLegalSAW_rebase m m' h h' ts).mpr hl)]
    simp only [numVertices, ofTurns]
  · rw [if_neg hl, if_neg (fun hc => hl ((hhe_isLegalSAW_rebase m m' h h' ts).mp hc))]


end StatMech.Universality
