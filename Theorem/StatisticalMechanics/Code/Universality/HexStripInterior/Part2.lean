/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Def.StatisticalMechanics.Code.Universality.HexStripInterior.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStrip_interiorVertices_core (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW)
    (hstay : hexStripStaysInDir dregion a h0 ts)
    (v : ℂ) (hv : v ∈ (HexWalk.ofTurns a h0 ts).vertices)
    (hvne : v ≠ hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)) :
    hexStripInterior dregion v := by
  have hvv : v ∈ HexWalk.verticesAux a h0 ts := hv
  obtain ⟨m', h', t', hm1, hm2, hveq, ht'⟩ := hexStrip_nonlast_dir a h0 ts v hvv hvne
  have hr1 : dregion m' h' := hstay (m', h') hm1
  have hr2 : dregion (m' + HexWalk.halfStep h' + HexWalk.halfStep (h' + t')) (h' + t') :=
    hstay _ hm2
  have htlegal : t' = 1 ∨ t' = -1 := hlegal.1 t' (by unfold HexWalk.ofTurns; exact ht')
  refine ⟨m', m' + HexWalk.halfStep h' + HexWalk.halfStep (h' + t'),
    h', h' + t', hr1, hr2, ?_, ?_, ?_⟩
  · 
    
    intro hc
    rw [Prod.mk.injEq] at hc
    have hzero : HexWalk.halfStep h' + HexWalk.halfStep (h' + t') = 0 := by
      have : m' + (HexWalk.halfStep h' + HexWalk.halfStep (h' + t')) = m' + 0 := by
        rw [add_zero, ← add_assoc]; exact hc.1.symm
      exact add_left_cancel this
    exact hexW1_halfStep_add_ne_zero h' t' htlegal hzero
  · 
    left; exact hveq
  · 
    right; rw [hexW1Exit_halfStep_add_three, hveq]; ring


end StatMech.Universality
