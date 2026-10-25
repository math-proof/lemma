/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Def.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


@[simp] theorem hexInfra_stepIncrements_nil (h : ℤ) : hexInfra_stepIncrements h [] = [] := rfl

@[simp] theorem hexInfra_stepIncrements_cons (h t : ℤ) (ts : List ℤ) :
    hexInfra_stepIncrements h (t :: ts)
      = ((HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re)
          :: hexInfra_stepIncrements (h + t) ts := rfl


theorem hexInfra_stepReSum_eq_sum_increments (h : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h ts = (hexInfra_stepIncrements h ts).sum := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih => rw [hexInfra_stepReSum_cons, hexInfra_stepIncrements_cons, List.sum_cons, ih]


theorem hexInfra_stepReSum_ge_of_advance (h : ℤ) (ts : List ℤ) (δ : ℝ)
    (hadv : ∀ x ∈ hexInfra_stepIncrements h ts, δ ≤ x) :
    (δ * ts.length : ℝ) ≤ hexInfra_stepReSum h ts := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih =>
    rw [hexInfra_stepReSum_cons, List.length_cons]
    have hhead : δ ≤ (HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re :=
      hadv _ (by rw [hexInfra_stepIncrements_cons]; exact List.mem_cons_self)
    have htail : ∀ x ∈ hexInfra_stepIncrements (h + t) ts, δ ≤ x := fun x hx =>
      hadv x (by rw [hexInfra_stepIncrements_cons]; exact List.mem_cons_of_mem _ hx)
    have := ih (h + t) htail
    push_cast
    nlinarith [this, hhead]


theorem hexInfra_reachesWidth_of_last_re (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (hdisp : (T : ℝ)
      ≤ hexInfra_stepReSum h0 ts + (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re) :
    hexWall3_ReachesWidth a h0 T ts := by
  refine ⟨hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts), ?_, ?_⟩
  · exact hexInfra_verticesAux_getLast_mem a h0 ts
  · rw [hexInfra_ofTurns_last_re]; linarith


theorem hexInfra_reachesWidth_of_advance (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) (δ : ℝ)
    (hadv : ∀ x ∈ hexInfra_stepIncrements h0 ts, δ ≤ x)
    (hlast : 0 ≤ (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re)
    (hsteps : (T : ℝ) ≤ δ * ts.length) :
    hexWall3_ReachesWidth a h0 T ts := by
  apply hexInfra_reachesWidth_of_last_re a h0 T ts
  have := hexInfra_stepReSum_ge_of_advance h0 ts δ hadv
  linarith


theorem hexInfra_singleRight_stepReSum :
    hexInfra_stepReSum 0 [(-1 : ℤ)] + (HexWalk.halfStep (hexInfra_headAccum 0 [(-1 : ℤ)])).re
      = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re := by
  simp only [hexInfra_stepReSum_cons, hexInfra_stepReSum_nil, hexInfra_headAccum_cons,
    hexInfra_headAccum_nil]
  rw [show (0 : ℤ) + (-1) = -1 by ring]
  ring


theorem hexInfra_singleRight_reaches (a : ℂ) :
    hexWall3_ReachesWidth a 0 1 [(-1 : ℤ)] :=
  hexWall3_reachesWidth_witness a

end StatMech.Universality
