/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhasePerturbation.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseCancellation.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem mem_sixVertexBetheMLBoundarySet {n : Nat}
    (w : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheMLBoundarySet w ↔
      i ∉ w ∧ finRotate (n + 1) i ∈ w := by
  simp [sixVertexBetheMLBoundarySet]


theorem exists_sixVertexBetheMLBoundary_away_of_one_lt_card
    {n : Nat} (w : Finset (Fin (n + 1)))
    (hcard : 1 < (sixVertexBetheMLBoundarySet w).card)
    (a : Fin (n + 1)) :
    ∃ i ∈ sixVertexBetheMLBoundarySet w,
      i ≠ a ∧ finRotate (n + 1) i ≠ a := by
  let b := (finRotate (n + 1)).symm a
  by_cases hb : b ∈ sixVertexBetheMLBoundarySet w
  · obtain ⟨i, hi, hib⟩ :=
      (sixVertexBetheMLBoundarySet w).exists_mem_ne hcard b
    refine ⟨i, hi, ?_, ?_⟩
    · intro hia
      subst i
      have hb' := (mem_sixVertexBetheMLBoundarySet w b).mp hb
      have ha' := (mem_sixVertexBetheMLBoundarySet w a).mp hi
      exact ha'.1 (by simpa [b] using hb'.2)
    · intro hrot
      apply hib
      apply (finRotate (n + 1)).injective
      simpa [b] using hrot
  · obtain ⟨i, hi, hia⟩ :=
      (sixVertexBetheMLBoundarySet w).exists_mem_ne hcard a
    refine ⟨i, hi, hia, ?_⟩
    intro hrot
    apply hb
    have : i = b := by
      apply (finRotate (n + 1)).injective
      simpa [b] using hrot
    simpa [this] using hi


theorem sum_sixVertexBethePerturbedWordTerm_adjacent_fixed_zeroSlot_eq_zero
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) (i : Fin n)
    (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (a : Fin (n + 1)) (ha : a ≠ i.castSucc) (hb : a ≠ i.succ)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell,
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  let tau := Equiv.swap i.castSucc i.succ
  let F : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
    if sigma a = ell then
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
    else 0
  have hsum : (∑ sigma, F sigma) = 0 := by
    apply sum_perm_eq_zero_of_swap_neg i.castSucc i.succ
    intro sigma
    have hfix : (sigma * tau) a = sigma a := by
      simp [tau, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne ha hb]
    by_cases hsigma : sigma a = ell
    · have hswap : (sigma * tau) a = ell := hfix.trans hsigma
      have hleft : sigma i.castSucc ≠ ell := by
        intro h
        exact ha (sigma.injective (hsigma.trans h.symm))
      have hright : sigma i.succ ≠ ell := by
        intro h
        exact hb (sigma.injective (hsigma.trans h.symm))
      rw [show F (sigma * tau) =
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * tau) by simp [F, hswap],
        show F sigma =
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma by
            simp [F, hsigma]]
      exact sixVertexBethePerturbedWordTerm_adjacent_cancel
        hc p ell eps x w i hiM hiL hphase sigma hleft hright
    · have hswap : (sigma * tau) a ≠ ell := by
        rw [hfix]
        exact hsigma
      rw [show F (sigma * tau) = 0 by
          apply if_neg
          exact hswap,
        show F sigma = 0 by simp [F, hsigma]]
      simp
  rw [Finset.sum_filter]
  simpa [F] using hsum


theorem sum_sixVertexBethePerturbedWordTerm_boundary_fixed_zeroSlot_eq_zero
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (hlastM : Fin.last (n + 1) ∉ w) (hzeroL : (0 : Fin (n + 2)) ∈ w)
    (a : Fin (n + 2)) (ha : a ≠ Fin.last (n + 1)) (hb : a ≠ 0)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma a = ell,
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  let tau := Equiv.swap (Fin.last (n + 1)) 0
  let F : Equiv.Perm (Fin (n + 2)) → Complex := fun sigma =>
    if sigma a = ell then
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
    else 0
  have hsum : (∑ sigma, F sigma) = 0 := by
    apply sum_perm_eq_zero_of_swap_neg (Fin.last (n + 1)) 0
    intro sigma
    have hfix : (sigma * tau) a = sigma a := by
      simp [tau, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne ha hb]
    by_cases hsigma : sigma a = ell
    · have hswap : (sigma * tau) a = ell := hfix.trans hsigma
      have hleft : sigma (Fin.last (n + 1)) ≠ ell := by
        intro h
        exact ha (sigma.injective (hsigma.trans h.symm))
      have hright : sigma 0 ≠ ell := by
        intro h
        exact hb (sigma.injective (hsigma.trans h.symm))
      rw [show F (sigma * tau) =
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * tau) by simp [F, hswap],
        show F sigma =
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma by
            simp [F, hsigma]]
      exact sixVertexBethePerturbedWordTerm_boundary_cancel
        hc p hp ell eps x w hlastM hzeroL hphase sigma hleft hright
    · have hswap : (sigma * tau) a ≠ ell := by
        rw [hfix]
        exact hsigma
      rw [show F (sigma * tau) = 0 by
          apply if_neg
          exact hswap,
        show F sigma = 0 by simp [F, hsigma]]
      simp
  rw [Finset.sum_filter]
  simpa [F] using hsum


theorem sum_sixVertexBethePerturbedWordTerm_eq_sum_fixed_zeroSlot
    {N n : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) =
      ∑ a : Fin (n + 1),
        ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell,
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
  symm
  calc
    (∑ a : Fin (n + 1),
        ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell,
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) =
      ∑ a : Fin (n + 1), ∑ sigma : Equiv.Perm (Fin (n + 1)),
        if sigma a = ell then
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
        else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_filter]
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)), ∑ a : Fin (n + 1),
        if sigma a = ell then
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
        else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      have hiff (a : Fin (n + 1)) : sigma a = ell ↔
          a = sigma.symm ell := by
        constructor
        · intro h
          exact sigma.injective
            (h.trans (sigma.apply_symm_apply ell).symm)
        · rintro rfl
          exact sigma.apply_symm_apply ell
      simp only [hiff]
      simp


theorem sum_sixVertexBethePerturbedWordTerm_eq_zero_of_multiple_ML
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (hcard : 1 < (sixVertexBetheMLBoundarySet w).card)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 2)),
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  rw [sum_sixVertexBethePerturbedWordTerm_eq_sum_fixed_zeroSlot]
  apply Finset.sum_eq_zero
  intro a hauniv
  obtain ⟨i, hi, hia, hirot⟩ :=
    exists_sixVertexBetheMLBoundary_away_of_one_lt_card w hcard a
  have hiML := (mem_sixVertexBetheMLBoundarySet w i).mp hi
  by_cases hilast : i = Fin.last (n + 1)
  · subst i
    apply sum_sixVertexBethePerturbedWordTerm_boundary_fixed_zeroSlot_eq_zero
      hc p hp ell eps x w hiML.1
    · simpa using hiML.2
    · exact Ne.symm hia
    · exact Ne.symm (by simpa using hirot)
    · exact hphase
  · have hival : i.val < n + 1 := by
      have hle : i.val ≤ n + 1 := by omega
      have hne : i.val ≠ n + 1 := by
        intro h
        apply hilast
        apply Fin.ext
        simpa using h
      omega
    let j : Fin (n + 1) := ⟨i.val, hival⟩
    have hjcast : j.castSucc = i := by
      apply Fin.ext
      rfl
    have hjrot : finRotate (n + 2) i = j.succ := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last hilast]
      rfl
    apply sum_sixVertexBethePerturbedWordTerm_adjacent_fixed_zeroSlot_eq_zero
      hc p ell eps x w j
    · simpa [hjcast] using hiML.1
    · simpa [hjrot] using hiML.2
    · intro h
      exact hia (hjcast.symm.trans h.symm)
    · intro h
      exact hirot (hjrot.trans h.symm)
    · exact hphase

end
end StatMech.FrontierD
