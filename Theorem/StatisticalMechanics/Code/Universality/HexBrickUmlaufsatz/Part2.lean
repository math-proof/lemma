/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part2


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


namespace HexAWBrickCycle

theorem step_eq_sub {n : ℕ} [NeZero n]
    (C : HexAWBrickCycle n) (i : Fin n) :
    stepOf (C.direction i) =
      hexBrickPos (C.coord (i + 1)) - hexBrickPos (C.coord i) := by
  have h := hexBrickPos_neighbor (C.coord i) (C.edge i)
  rw [C.adjacent i] at h
  change hexBrickPos (C.coord (i + 1)) =
      hexBrickPos (C.coord i) + stepOf (C.direction i) at h
  rw [Prod.ext_iff] at h ⊢
  constructor <;>
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at h ⊢ <;>
    omega


theorem closed {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) :
    ∑ i, stepOf (C.direction i) = 0 := by
  rw [Finset.sum_congr rfl (fun i _ => C.step_eq_sub i),
    Finset.sum_sub_distrib]
  have hreindex :
      (∑ i : Fin n, hexBrickPos (C.coord (i + 1))) =
        ∑ i : Fin n, hexBrickPos (C.coord i) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun i => hexBrickPos (C.coord i))
  rw [hreindex, sub_self]


theorem pos_eq {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) (k : Fin n) :
    pos C.direction k =
      hexBrickPos (C.coord k) - hexBrickPos (C.coord 0) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction k using Fin.induction with
  | zero =>
      rw [StatMech.Onsager.NoDoubleWind.pos_zero]
      simp
  | succ i ih =>
      have hisucc : i.succ = i.castSucc + 1 := by
        apply Fin.ext
        simp
      rw [hisucc,
        StatMech.Onsager.NoDoubleWind.pos_succ C.direction C.closed i.castSucc,
        ← hisucc, ih]
      have hs := C.step_eq_sub i.castSucc
      rw [← hisucc] at hs
      rw [Prod.ext_iff] at hs ⊢
      constructor <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hs ⊢ <;>
        omega


theorem pos_injective {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) :
    Function.Injective (pos C.direction) := by
  intro i j hij
  rw [C.pos_eq i, C.pos_eq j] at hij
  have hbrick : hexBrickPos (C.coord i) = hexBrickPos (C.coord j) := by
    rw [Prod.ext_iff] at hij ⊢
    constructor <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hij ⊢ <;>
      omega
  exact C.coord_injective (hexBrickPos_injective hbrick)


end HexAWBrickCycle
end StatMech.Universality
