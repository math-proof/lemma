/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2


namespace StatMech.Universality

open Complex HexWalk Set


theorem hexContourSum_empty
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexContourSum inRegion a h0 ∅ x = 0 := by
  unfold hexContourSum
  letI : IsEmpty {ts // ts ∈ hexContourFamily inRegion a h0 (∅ : Set ℂ)} :=
    ⟨fun ts => by
      rcases ts.property.2.2 with ⟨z, hz, _⟩
      exact hz.elim⟩
  exact tsum_empty


theorem hexContourFamily_singleton_start
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (hreg : inRegion a) :
    hexContourFamily inRegion a h0 ({a} : Set ℂ) = {[]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hza : z = a := by simpa using hz
    subst z
    exact hexReturningLegalSAW_eq_nil a h0 ts hlegal hend
  · intro hts
    have hnil : ts = [] := by simpa using hts
    subst ts
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, a, by simp,
      trivialWalk_endMid a h0⟩
    intro m hm
    have hmids : (ofTurns a h0 ([] : List ℤ)).mids = [a] := by
      change (trivialWalk a h0).mids = [a]
      unfold HexWalk.mids trivialWalk
      simp [midsAux]
    rw [hmids] at hm
    exact (List.mem_singleton.mp hm) ▸ hreg


theorem hexContourSum_singleton_start
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (x : ℝ)
    (hreg : inRegion a) :
    hexContourSum inRegion a h0 ({a} : Set ℂ) x = x := by
  rw [hexContourSum, hexContourFamily_singleton_start inRegion a h0 hreg]
  let w0 : {ts : List ℤ // ts ∈ ({[]} : Set (List ℤ))} := ⟨[], by simp⟩
  rw [tsum_eq_single w0]
  · simp [w0, ofTurns]
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    change w.val = w0.val
    have hprop := w.property
    change w.val = [] at hprop
    exact hprop


end StatMech.Universality
