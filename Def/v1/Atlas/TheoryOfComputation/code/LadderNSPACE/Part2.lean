/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Structure.v1.Atlas.TheoryOfComputation.code.LadderNSPACE
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- Transition relation of the linear-space NTM deciding `LADDER_DFA`.
At the end of `readInput` it parses the buffer into a pair `(u, v)` of equal-length strings with
`u ∈ L(B)`, and either accepts immediately (if `u = v`) or enters `searchFwd` with `y := u` and
`counter := |α|^|u|` (the maximum possible number of rungs without repetition).
In `searchFwd` it nondeterministically guesses a position `i` and symbol `a`, sets
`y[i] := a`, checks that the new rung is in `L(B)`, and either accepts (if it equals `v`) or
continues. `searchBack` simply moves the head left between rungs. -/
noncomputable def ladderNTMδ {α : Type} {σ : Type}
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
    (B : DFA α σ) (q : LadderState α) (sym : LadderTapeSymbol α) :
    Set (LadderState α × LadderTapeSymbol α × Direction) := by
  classical
  exact match q.phase with
  | .readInput =>
      match sym with
      | .blank =>


        if h : ∃ (u v : List α), q.buf = encodePair u v ∧
            u.length = v.length ∧ u ∈ B.accepts then
          let u := h.choose
          let v := h.choose_spec.choose
          if u = v then

            {(⟨.accepted, [], [], [], 0⟩, sym, Direction.R)}
          else if u ∈ B.accepts then

            {(⟨.searchFwd, [], u, v, (Fintype.card α) ^ u.length⟩, sym, Direction.R)}
          else
            {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
        else
          {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
      | other => {(⟨.readInput, q.buf ++ [other], [], [], 0⟩, sym, Direction.R)}
  | .searchFwd =>


      if q.counter = 0 then

        {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
      else if h_len : q.y.length = 0 then

        {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
      else

        (Set.univ : Set (Fin q.y.length × α)).image fun ⟨i, a⟩ =>
          let new_y := q.y.set i.val a
          if ¬(new_y ∈ B.accepts) then
            (⟨.rejected, [], [], [], 0⟩, sym, Direction.R)
          else if new_y = q.v then
            (⟨.accepted, [], [], [], 0⟩, sym, Direction.R)
          else
            (⟨.searchBack, [], new_y, q.v, q.counter - 1⟩, sym, Direction.R)
  | .searchBack =>

      {(⟨.searchFwd, [], q.y, q.v, q.counter⟩, sym, Direction.L)}
  | .accepted => ∅
  | .rejected => ∅

/-- The linear-space NTM deciding `LADDER_DFA` for the DFA `B`. The state space is
`LadderState α`, the tape alphabet is `LadderTapeSymbol α`, and the transition relation is
`ladderNTMδ B`. The input alphabet consists of the lifted DFA symbols and the separator. -/
noncomputable def ladderNTM {α : Type} {σ : Type}
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
    (B : DFA α σ) :
    NTM (LadderState α) (LadderTapeSymbol α) where
  blank := .blank
  inputAlpha := Set.range LadderTapeSymbol.ofAlpha ∪ {LadderTapeSymbol.separator}
  blank_not_in_inputAlpha := by
    intro hmem
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨a, h⟩ | h <;> cases h
  δ := ladderNTMδ B
  q₀ := ⟨.readInput, [], [], [], 0⟩
  qAccept := ⟨.accepted, [], [], [], 0⟩
  qReject := ⟨.rejected, [], [], [], 0⟩
  qReject_ne_qAccept := by simp [LadderState.mk.injEq]


end SpaceComplexity
