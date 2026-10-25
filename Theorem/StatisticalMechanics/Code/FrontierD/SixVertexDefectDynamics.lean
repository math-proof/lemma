/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sum_update_add_old
    {n : Nat} (f : Fin n → Nat) (i : Fin n) (b : Nat) :
    (∑ j, Function.update f i b j) + f i = (∑ j, f j) + b := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  omega

theorem weighted_sum_update_add_old
    {n : Nat} (f : Fin n → Nat) (w : Fin n → Nat)
    (i : Fin n) (b : Nat) :
    (∑ j, w j * Function.update f i b j) + w i * f i =
      (∑ j, w j * f j) + w i * b := by
  have hfun : (fun j => w j * Function.update f i b j) =
      Function.update (fun j => w j * f j) i (w i * b) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  rw [hfun]
  exact sum_update_add_old (fun j => w j * f j) i (w i * b)

@[simp] theorem sixVertexDefectLower_apply_self
    {n : Nat} (d : Fin n → Nat) (i : Fin n) (hi : 0 < i.val) :
    sixVertexDefectLower d i hi i = d i - 1 := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  have hip : i ≠ p := by
    intro h
    have := congrArg Fin.val h
    dsimp [p] at this
    omega
  change Function.update (Function.update d i (d i - 1)) p
      (d p + 1) i = d i - 1
  rw [Function.update_of_ne hip, Function.update_self]

@[simp] theorem sixVertexDefectLower_apply_pred
    {n : Nat} (d : Fin n → Nat) (i : Fin n) (hi : 0 < i.val) :
    sixVertexDefectLower d i hi ⟨i.val - 1, by omega⟩ =
      d ⟨i.val - 1, by omega⟩ + 1 := by
  simp [sixVertexDefectLower]

theorem sum_sixVertexDefectLower
    {n : Nat} (d : Fin n → Nat) (i : Fin n)
    (hi : 0 < i.val) (hd : 0 < d i) :
    ∑ j, sixVertexDefectLower d i hi j = ∑ j, d j := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let f := Function.update d i (d i - 1)
  have hpi : p ≠ i := by
    intro h
    have := congrArg Fin.val h
    dsimp [p] at this
    omega
  have hfi : f p = d p := by
    simp [f, Function.update_of_ne hpi]
  have hfirst := sum_update_add_old d i (d i - 1)
  have hsecond := sum_update_add_old f p (d p + 1)
  change (∑ j, f j) + d i = (∑ j, d j) + (d i - 1) at hfirst
  change (∑ j, Function.update f p (d p + 1) j) + f p =
    (∑ j, f j) + (d p + 1) at hsecond
  rw [hfi] at hsecond
  have hfirst' : (∑ j, f j) + 1 = ∑ j, d j := by omega
  have hsecond' :
      (∑ j, Function.update f p (d p + 1) j) =
        (∑ j, f j) + 1 := by omega
  change (∑ j, Function.update f p (d p + 1) j) = ∑ j, d j
  rw [hsecond', hfirst']

theorem sixVertexDefectWeight_lower_add_one
    {n : Nat} (d : Fin n → Nat) (i : Fin n)
    (hi : 0 < i.val) (hd : 0 < d i) :
    sixVertexDefectWeight (sixVertexDefectLower d i hi) + 1 =
      sixVertexDefectWeight d := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let f := Function.update d i (d i - 1)
  have hpi : p ≠ i := by
    intro h
    have := congrArg Fin.val h
    dsimp [p] at this
    omega
  have hfi : f p = d p := by
    simp [f, Function.update_of_ne hpi]
  have hfirst := weighted_sum_update_add_old d (fun j => j.val) i (d i - 1)
  have hsecond := weighted_sum_update_add_old f (fun j => j.val) p (d p + 1)
  change (∑ j, j.val * f j) + i.val * d i =
    (∑ j, j.val * d j) + i.val * (d i - 1) at hfirst
  change (∑ j, j.val * Function.update f p (d p + 1) j) + p.val * f p =
    (∑ j, j.val * f j) + p.val * (d p + 1) at hsecond
  rw [hfi] at hsecond
  have hdi : d i = d i - 1 + 1 := by omega
  have hmulI : i.val * d i = i.val * (d i - 1) + i.val := by
    calc
      i.val * d i = i.val * (d i - 1 + 1) :=
        congrArg (fun q => i.val * q) hdi
      _ = i.val * (d i - 1) + i.val := by rw [Nat.mul_add, Nat.mul_one]
  have hmulP : p.val * (d p + 1) = p.val * d p + p.val := by
    rw [Nat.mul_add, Nat.mul_one]
  have hpval : p.val + 1 = i.val := by
    dsimp [p]
    omega
  have hfirst' : (∑ j, j.val * f j) + i.val =
      ∑ j, j.val * d j := by omega
  have hsecond' :
      (∑ j, j.val * Function.update f p (d p + 1) j) =
        (∑ j, j.val * f j) + p.val := by omega
  change (∑ j, j.val * Function.update f p (d p + 1) j) + 1 =
    ∑ j, j.val * d j
  omega

theorem sixVertexDefectWeight_eq_zero_iff
    {n : Nat} (d : Fin n → Nat) :
    sixVertexDefectWeight d = 0 ↔ ∀ i, 0 < i.val → d i = 0 := by
  rw [sixVertexDefectWeight, Finset.sum_eq_zero_iff]
  constructor
  · intro h i hi
    have := h i (Finset.mem_univ i)
    rcases Nat.mul_eq_zero.mp this with hival | hdi
    · exact False.elim (Nat.ne_of_gt hi hival)
    · exact hdi
  · intro h i _
    by_cases hi : i.val = 0
    · simp [hi]
    · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
      rw [h i hipos, mul_zero]

theorem sixVertexDefectPile_sum
    {n : Nat} (hn : 0 < n) (D : Nat) :
    ∑ i, sixVertexDefectPile hn D i = D := by
  let z : Fin n := ⟨0, hn⟩
  rw [Finset.sum_eq_single_of_mem z (Finset.mem_univ z)]
  · simp [sixVertexDefectPile, z]
  · intro i _ hiz
    have hi : i.val ≠ 0 := by
      intro h
      apply hiz
      exact Fin.ext h
    simp [sixVertexDefectPile, hi]

theorem sixVertexDefect_eq_pile_of_weight_eq_zero
    {n : Nat} (hn : 0 < n) (d : Fin n → Nat)
    (hweight : sixVertexDefectWeight d = 0) :
    d = sixVertexDefectPile hn (∑ i, d i) := by
  have hoff := (sixVertexDefectWeight_eq_zero_iff d).mp hweight
  let z : Fin n := ⟨0, hn⟩
  have hsum : (∑ i, d i) = d z := by
    apply Finset.sum_eq_single_of_mem z (Finset.mem_univ z)
    intro i _ hiz
    have hi : 0 < i.val := by
      have hine : i.val ≠ 0 := by
        intro h
        apply hiz
        exact Fin.ext h
      omega
    exact hoff i hi
  funext i
  by_cases hi : i.val = 0
  · have hiz : i = z := Fin.ext hi
    subst i
    simp [sixVertexDefectPile, z, hsum]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
    rw [hoff i hipos]
    simp [sixVertexDefectPile, hi]


theorem sixVertexDefectLowerStep_reaches_pile
    {n : Nat} (hn : 0 < n) (d : Fin n → Nat) :
    Relation.ReflTransGen SixVertexDefectLowerStep d
      (sixVertexDefectPile hn (∑ i, d i)) := by
  by_cases hw0 : sixVertexDefectWeight d = 0
  · have hd := sixVertexDefect_eq_pile_of_weight_eq_zero hn d hw0
    rw [hd, sixVertexDefectPile_sum]
  · have hwpos : 0 < sixVertexDefectWeight d := Nat.pos_of_ne_zero hw0
    rw [sixVertexDefectWeight] at hwpos
    obtain ⟨i, _, hiweight⟩ := Finset.sum_pos_iff.mp hwpos
    have hi : 0 < i.val := Nat.pos_of_mul_pos_right hiweight
    have hd : 0 < d i := Nat.pos_of_mul_pos_left hiweight
    let e := sixVertexDefectLower d i hi
    have hstep : SixVertexDefectLowerStep d e := ⟨i, hi, hd, rfl⟩
    have hreach := sixVertexDefectLowerStep_reaches_pile hn e
    have hsum := sum_sixVertexDefectLower d i hi hd
    exact (Relation.ReflTransGen.single hstep).trans (by
      simpa only [e, hsum] using hreach)
termination_by sixVertexDefectWeight d
decreasing_by
  have hweight := sixVertexDefectWeight_lower_add_one d i hi hd
  omega

theorem SixVertexDefectLowerStep.sum_eq
    {n : Nat} {d e : Fin n → Nat} (h : SixVertexDefectLowerStep d e) :
    ∑ i, e i = ∑ i, d i := by
  obtain ⟨i, hi, hd, rfl⟩ := h
  exact sum_sixVertexDefectLower d i hi hd

theorem SixVertexDefectLowerStep.weight_add_one
    {n : Nat} {d e : Fin n → Nat} (h : SixVertexDefectLowerStep d e) :
    sixVertexDefectWeight e + 1 = sixVertexDefectWeight d := by
  obtain ⟨i, hi, hd, rfl⟩ := h
  exact sixVertexDefectWeight_lower_add_one d i hi hd


end
end StatMech.FrontierD
