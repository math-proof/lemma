/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_subtype_eq_sum_ite {Omega : Type} [Fintype Omega]
    (p : Omega → Prop) [DecidablePred p] :
    Nat.card {x : Omega // p x} = ∑ x : Omega, if p x then 1 else 0 := by
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {x : Omega // p x} =
        Fintype.card (↑(Finset.univ.filter p)) :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
    _ = (Finset.univ.filter p).card := Fintype.card_coe _
    _ = ∑ x : Omega, if p x then 1 else 0 := by
      rw [Finset.card_filter]


theorem finiteUniformCoupling_fiber_l1_le
    {Omega A : Type} [Fintype Omega] [Fintype A] [DecidableEq A]
    (e : Omega ≃ Omega) (f g : Omega → A) :
    ∑ a : A, |((Nat.card {w : Omega // f w = a} : Nat) : Real) -
      ((Nat.card {w : Omega // g w = a} : Nat) : Real)| ≤
      2 * ((Nat.card {w : Omega // f w ≠ g (e w)} : Nat) : Real) := by
  classical
  have hfiber (a : A) :
      (((Nat.card {w : Omega // f w = a} : Nat) : Real) -
          ((Nat.card {w : Omega // g w = a} : Nat) : Real)) =
        ∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real) := by
    rw [natCard_subtype_eq_sum_ite, natCard_subtype_eq_sum_ite]
    push_cast
    rw [Finset.sum_sub_distrib]
    congr 1
    exact (Equiv.sum_comp e
      (fun w : Omega => if g w = a then (1 : Real) else 0)).symm
  rw [show (∑ a : A, |((Nat.card {w : Omega // f w = a} : Nat) : Real) -
      ((Nat.card {w : Omega // g w = a} : Nat) : Real)|) =
      ∑ a : A, |∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfiber a]]
  calc
    (∑ a : A, |∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)|) ≤
        ∑ a : A, ∑ w : Omega, |((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w : Omega, ∑ a : A, |((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| := Finset.sum_comm
    _ = ∑ w : Omega, if f w ≠ g (e w) then (2 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : f w = g (e w)
      · simp [h]
      · rw [if_pos h]
        calc
          (∑ a : A, |((if f w = a then 1 else 0) -
              (if g (e w) = a then 1 else 0) : Real)|) =
              ∑ a : A, ((if f w = a then 1 else 0) +
                (if g (e w) = a then 1 else 0) : Real) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hf : f w = a
            · have hg : g (e w) ≠ a := by
                intro hga
                exact h (hf.trans hga.symm)
              simp [hf, hg]
            · by_cases hg : g (e w) = a <;> simp [hf, hg]
          _ = (∑ a : A, (if f w = a then (1 : Real) else 0)) +
              ∑ a : A, (if g (e w) = a then (1 : Real) else 0) :=
            Finset.sum_add_distrib
          _ = 2 := by simp; norm_num
    _ = 2 * ((Nat.card {w : Omega // f w ≠ g (e w)} : Nat) : Real) := by
      rw [natCard_subtype_eq_sum_ite]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : f w ≠ g (e w) <;> simp [h]

theorem firstHitSplit_eq_none_of_endpoint_fst_ne
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (havoid : ∀ k, k ≤ path.length →
      (isingDiagonalWalkEndpoint start (path.take k)).1 ≠ level) :
    isingDiagonalWalkFirstHitSplit? start level path = none := by
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => rfl
  | some split =>
      exfalso
      have hsteps := firstHitSplit_steps hsplit
      have hk : split.before.length ≤ path.length := by
        rw [← hsteps]
        simp [IsingDiagonalWalkHitSplit.steps]
      exact (havoid split.before.length hk) (by
        have htake : path.take split.before.length = split.before := by
          rw [← hsteps]
          simp [IsingDiagonalWalkHitSplit.steps]
        rw [htake]
        exact split.hit)

theorem reflectAll_endpoint_take_fst
    (path : List (Int × Int)) (start : Int × Int) (level : Int)
    (k : Nat) :
    (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
      ((path.map reflectIncrement).take k)).1 =
        2 * level -
          (isingDiagonalWalkEndpoint start (path.take k)).1 := by
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint reflectedEndpoint
    isingDiagonalWalkDisplacement
  simp only [List.map_map]
  have hneg :
      ((path.take k).map (fun d => -d.1)).sum =
        -((path.take k).map Prod.fst).sum := by
    induction path.take k with
    | nil => simp
    | cons d ds ih => simp [ih, add_comm]
  change (2 * level - start.1) +
      ((path.take k).map (fun d => -d.1)).sum =
    2 * level - (start.1 + ((path.take k).map Prod.fst).sum)
  rw [hneg]
  ring

theorem reflectAll_valid (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path) :
    IsingDiagonalWalkStepsValid (path.map reflectIncrement) := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
  have heValid := hvalid e he
  rcases heValid with ⟨hex, hey⟩
  constructor
  · rcases hex with hex | hex <;> simp [reflectIncrement, hex]
  · simpa [reflectIncrement] using hey

theorem firstHitSplit_reflectAll_eq_none
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (hnone : isingDiagonalWalkFirstHitSplit? start level path = none) :
    isingDiagonalWalkFirstHitSplit? (reflectedEndpoint level start) level
      (path.map reflectIncrement) = none := by
  apply firstHitSplit_eq_none_of_endpoint_fst_ne
  intro k hk heq
  have horig := firstHitSplit_none_endpoint_fst_ne hnone k (by simpa using hk)
  have hreflect := reflectAll_endpoint_take_fst path start level k
  rw [heq] at hreflect
  apply horig
  omega


end
end StatMech.Universality
