/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22


namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

theorem natCard_subtype_eq_sum_ite_pointwise
    {Omega : Type*} [Fintype Omega]
    (p : Omega -> Prop) [DecidablePred p] :
    Nat.card {x : Omega // p x} =
      ∑ x : Omega, if p x then 1 else 0 := by
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {x : Omega // p x} =
        Fintype.card (↑(Finset.univ.filter p)) :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
    _ = (Finset.univ.filter p).card := Fintype.card_coe _
    _ = ∑ x : Omega, if p x then 1 else 0 := by
      rw [Finset.card_filter]


theorem finiteUniformCoupling_fiber_abs_le_badAt
    {Omega A : Type*} [Fintype Omega] [Fintype A] [DecidableEq A]
    (e : Omega ≃ Omega) (f g : Omega -> A) (a : A) :
    |((Nat.card {w : Omega // f w = a} : Nat) : Real) -
        ((Nat.card {w : Omega // g w = a} : Nat) : Real)| <=
      (Nat.card {w : Omega //
        f w ≠ g (e w) /\ (f w = a \/ g (e w) = a)} : Nat) := by
  classical
  have hfiber :
      (((Nat.card {w : Omega // f w = a} : Nat) : Real) -
          ((Nat.card {w : Omega // g w = a} : Nat) : Real)) =
        ∑ w : Omega, ((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real) := by
    rw [natCard_subtype_eq_sum_ite_pointwise,
      natCard_subtype_eq_sum_ite_pointwise]
    push_cast
    rw [Finset.sum_sub_distrib]
    congr 1
    exact (Equiv.sum_comp e
      (fun w : Omega => if g w = a then (1 : Real) else 0)).symm
  rw [hfiber]
  calc
    |∑ w : Omega, ((if f w = a then 1 else 0) -
        (if g (e w) = a then 1 else 0) : Real)| <=
        ∑ w : Omega, |((if f w = a then 1 else 0) -
          (if g (e w) = a then 1 else 0) : Real)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w : Omega,
        if f w ≠ g (e w) /\ (f w = a \/ g (e w) = a)
        then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hf : f w = a
      · by_cases hg : g (e w) = a
        · simp [hf, hg]
        · have hane : a ≠ g (e w) := fun h => hg h.symm
          simp [hf, hg, hane]
      · by_cases hg : g (e w) = a
        · simp [hf, hg]
        · simp [hf, hg]
    _ = (Nat.card {w : Omega //
        f w ≠ g (e w) /\ (f w = a \/ g (e w) = a)} : Nat) := by
      rw [natCard_subtype_eq_sum_ite_pointwise]
      push_cast
      rfl


end StatMech.Universality
