/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

@[simp] theorem hexCSBrickDirections_nil (h : ℤ) :
    hexCSBrickDirections h [] = [hexBrickDir (hexCSHeadingFin h)] := rfl

@[simp] theorem hexCSBrickDirections_cons (h t : ℤ) (ts : List ℤ) :
    hexCSBrickDirections h (t :: ts) =
      hexBrickDir (hexCSHeadingFin h) ::
        hexCSBrickDirections (h + t) ts := rfl

@[simp] theorem hexCSBrickDirections_length (h : ℤ) (ts : List ℤ) :
    (hexCSBrickDirections h ts).length = ts.length + 1 := by
  simp [hexCSBrickDirections, length_headingsAux]

theorem hexCSBrickDirections_ne_nil (h : ℤ) (ts : List ℤ) :
    hexCSBrickDirections h ts ≠ [] := by
  intro he
  have := congrArg List.length he
  simp at this

@[simp] theorem hexCSBrickDirections_head (h : ℤ) (ts : List ℤ) :
    (hexCSBrickDirections h ts).head! =
      hexBrickDir (hexCSHeadingFin h) := by
  cases ts <;> rfl

@[simp] theorem hexCSBrickDirections_getLast (h : ℤ) (ts : List ℤ) :
    (hexCSBrickDirections h ts).getLast! =
      hexBrickDir (hexCSHeadingFin (hexInfra_headAccum h ts)) := by
  induction ts generalizing h with
  | nil => rfl
  | cons t ts ih =>
      rw [hexCSBrickDirections_cons]
      have htail : hexCSBrickDirections (h + t) ts ≠ [] :=
        hexCSBrickDirections_ne_nil _ _
      rw [ons_getLast!_eq_getLast _ (List.cons_ne_nil _ _),
        List.getLast_cons htail,
        ← ons_getLast!_eq_getLast _ htail, ih]
      rfl


theorem hexCS_brick_open_telescope (h : ℤ) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    2 * ts.sum + 3 * ons_openTurnSum (hexCSBrickDirections h ts) =
      hexBrickTurnPotential
          (hexCSHeadingFin (hexInfra_headAccum h ts)) -
        hexBrickTurnPotential (hexCSHeadingFin h) := by
  induction ts generalizing h with
  | nil => simp [hexInfra_headAccum]
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      have hlocal := hexBrick_local_turn_identity
        (hexCSHeadingFin h) t ht
      rw [← hexCSHeadingFin_turn h t ht] at hlocal
      have hdirs : hexCSBrickDirections (h + t) ts ≠ [] :=
        hexCSBrickDirections_ne_nil _ _
      obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hdirs
      have hdval : d = hexBrickDir (hexCSHeadingFin (h + t)) := by
        have heq := congrArg List.head! hd
        rw [hexCSBrickDirections_head] at heq
        simpa using heq.symm
      rw [hexCSBrickDirections_cons, hd,
        ons_openTurnSum_cons_cons, ← hd]
      rw [hdval]
      simp only [List.sum_cons, hexInfra_headAccum_cons]
      have hi := ih (h + t) htail
      omega


end
end StatMech.Universality
