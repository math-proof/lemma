/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordSplit.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val)
    (hclean : polygon.ChordIsClean 0 j)
    (hd : 2 ≤ (-j).val)
    (hcleanRotated : (polygon.rotate j).ChordIsClean 0 (-j))
    (hcompatible : polygon.CleanChordBoundaryPhaseCompatible j (by omega))
    (hfirst : kwVectorPhaseCycle
      (polygon.prefixOfCleanChord j hj hclean).edgeList = -1)
    (hsecond : kwVectorPhaseCycle
      ((polygon.rotate j).prefixOfCleanChord (-j) hd
        hcleanRotated).edgeList = -1) :
    kwVectorPhaseCycle polygon.edgeList = -1 := by
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let chord := polygon.vertex j - polygon.vertex 0
  have hj0 : j ≠ 0 := by
    apply Fin.ne_of_val_ne
    simpa using (show j.val ≠ 0 by omega)
  have hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  have hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  have hp : kwVectorPhaseCycle (p.concat (-chord)) = -1 := by
    rw [polygon.prefixOfCleanChord_edgeList_eq_take j hj hclean] at hfirst
    simpa only [p, chord, neg_sub] using hfirst
  have hq : kwVectorPhaseCycle (q.concat chord) = -1 := by
    rw [polygon.complementOfCleanChord_edgeList_eq_drop
      j hj0 hd hcleanRotated] at hsecond
    simpa only [q, chord] using hsecond
  have hboundary :
      kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
          kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
        -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
            kwVectorTurnPhase (-chord) (p.head hpne) *
          (kwVectorTurnPhase (q.getLast hqne) chord *
            kwVectorTurnPhase chord (q.head hqne))) := by
    simpa only [KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible,
      p, q, chord] using hcompatible
  rw [← List.take_append_drop j.val polygon.edgeList]
  exact kwVectorPhaseCycle_chord_glue_lists_eq_neg_one
    p q hpne hqne chord hboundary hp hq


theorem kwVectorPhaseCycle_contract_front_remaining
    (incoming outgoing : ℂ) (remaining : List ℂ)
    (hne : remaining ≠ []) (htail : remaining.tail ≠ [])
    (hlocal :
      kwVectorTurnPhase (remaining.tail.getLast htail) incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing (remaining.head hne) =
        kwVectorTurnPhase (remaining.tail.getLast htail)
            (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) (remaining.head hne)) :
    kwVectorPhaseCycle (incoming :: outgoing :: remaining) =
      kwVectorPhaseCycle ((incoming + outgoing) :: remaining) := by
  obtain ⟨next, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hrest : rest ≠ [] := by simpa using htail
  let previous := rest.getLast hrest
  let tail := rest.dropLast
  have hrestEq : rest = tail ++ [previous] := by
    exact (rest.dropLast_append_getLast hrest).symm
  have hcontract := kwVectorPhaseCycle_contract_of_local
    previous incoming outgoing next tail (by simpa [previous] using hlocal)
  have horiginal := kwVectorPhaseCycle_rotate
    (previous :: incoming :: outgoing :: next :: tail) 1
  have hreduced := kwVectorPhaseCycle_rotate
    (previous :: (incoming + outgoing) :: next :: tail) 1
  simp only [List.rotate_cons_succ, List.rotate_zero] at horiginal hreduced
  rw [hrestEq]
  simpa only [List.singleton_append, List.cons_append] using
    horiginal.trans (hcontract.trans hreduced.symm)


theorem KWFiniteSimplePolygon.phaseCycle_removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple)
    (hphase : polygon.VertexOnePhaseEar hm) :
    kwVectorPhaseCycle polygon.edgeList =
      kwVectorPhaseCycle (polygon.removeVertexOne hm hsimple).edgeList := by
  let remaining := List.ofFn (fun i : Fin (m + 1) ↦
    polygon.edgeVector i.succ.succ)
  have hne : remaining ≠ [] := by simp [remaining]
  have htail : remaining.tail ≠ [] := by
    simp [remaining]
    omega
  rw [KWFiniteSimplePolygon.edgeList_eq_cyclic,
    kwCyclicEdgeList_eq_first_two]
  rw [polygon.removeVertexOne_edgeList hm hsimple]
  apply kwVectorPhaseCycle_contract_front_remaining
    (polygon.edgeVector 0) (polygon.edgeVector 1) remaining hne htail
  simpa only [remaining, KWFiniteSimplePolygon.VertexOnePhaseEar] using hphase

end StatMech.FrontierA
