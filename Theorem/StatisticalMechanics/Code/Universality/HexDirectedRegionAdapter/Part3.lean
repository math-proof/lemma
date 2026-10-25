/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part3


namespace StatMech.Universality

open Complex HexWalk


theorem hexStripInterior_of_distinctMidpoint
    (dregion : ℂ → ℤ → Prop) (v : ℂ)
    (hv : hexStripInteriorDistinctMidpoint dregion v) :
    hexStripInterior dregion v := by
  rcases hv with ⟨m1, m2, d1, d2, hm1, hm2, hne, hi1, hi2⟩
  exact ⟨m1, m2, d1, d2, hm1, hm2, fun hp => hne (congrArg Prod.fst hp),
    hi1, hi2⟩


theorem hexStrip_interiorVertices_distinctMidpoint_core
    (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : hexStripStaysInDir dregion a h0 ts)
    (v : ℂ) (hv : v ∈ (ofTurns a h0 ts).vertices)
    (hvne : v ≠ hexInfra_midAccum a h0 ts
      + halfStep (hexInfra_headAccum h0 ts)) :
    hexStripInteriorDistinctMidpoint dregion v := by
  have hvv : v ∈ verticesAux a h0 ts := hv
  obtain ⟨m', h', t', hm1, hm2, hveq, ht'⟩ :=
    hexStrip_nonlast_dir a h0 ts v hvv hvne
  have hr1 : dregion m' h' := hstay (m', h') hm1
  have hr2 : dregion
      (m' + halfStep h' + halfStep (h' + t')) (h' + t') :=
    hstay _ hm2
  have htlegal : t' = 1 ∨ t' = -1 :=
    hlegal.1 t' (by unfold ofTurns; exact ht')
  refine ⟨m', m' + halfStep h' + halfStep (h' + t'),
    h', h' + t', hr1, hr2, ?_, ?_, ?_⟩
  · intro hc
    have hzero : halfStep h' + halfStep (h' + t') = 0 := by
      have heq : m' + (halfStep h' + halfStep (h' + t')) = m' + 0 := by
        rw [add_zero, ← add_assoc]
        exact hc.symm
      exact add_left_cancel heq
    exact hexW1_halfStep_add_ne_zero h' t' htlegal hzero
  · left
    exact hveq
  · right
    rw [hexW1Exit_halfStep_add_three, hveq]
    ring


end StatMech.Universality
