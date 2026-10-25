/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseConstant.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheWordMonomial_erase_zero_zip_adjacent
    {N n : Nat} (p : Fin (n + 1) → Real) (ell : Fin (n + 1))
    (hell : p ell = 0) (sigma : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → Int) (w : Finset (Fin (n + 1)))
    (i : Fin n) (hiL : i.castSucc ∈ w) (hsuccL : i.succ ∈ w)
    (hzero : sigma i.castSucc = ell) :
    sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
        (sigma * Equiv.swap i.castSucc i.succ) x (w.erase i.castSucc) =
      sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
        sigma x w := by
  let w' := w.erase i.castSucc
  have hiM' : i.castSucc ∉ w' := by simp [w']
  have hsuccL' : i.succ ∈ w' := by
    simp [w', hsuccL]
    intro h
    have := congrArg Fin.val h
    simp at this
  rw [sixVertexBetheWordMonomial_adjacent_invariant
    (N := N) (fun j => sixVertexBethePhase (p j)) sigma x w' i
      hiM' hsuccL']
  unfold sixVertexBetheWordMonomial
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hki : k = i.castSucc
  · subst k
    simp [w', hiL, hzero, hell, sixVertexBethePhase]
  · simp [w', hki]

theorem sixVertexBetheZeroHatCoefficient_zip_adjacent
    {c : Real} (hc : 2 < c) {n : Nat}
    (p : Fin (n + 1) → Real) (sigma : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) (a : Fin (n + 1)) (i : Fin n)
    (hrot : finRotate (n + 1) a = i.castSucc)
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (hiL : i.castSucc ∈ w) (hsuccL : i.succ ∈ w) :
    sixVertexBetheZeroHatCoefficient c p
        (sigma * Equiv.swap i.castSucc i.succ)
        (w.erase i.castSucc) i.castSucc *
        sixVertexBetheL c (sixVertexBethePhase (p (sigma i.succ))) =
      sixVertexBetheZeroHatCoefficient c p sigma w a *
        sixVertexBetheM c (sixVertexBethePhase (p (sigma i.succ))) := by
  let b : Fin (n + 1) := i.castSucc
  let d : Fin (n + 1) := i.succ
  let w' := w.erase b
  let sigma' := sigma * Equiv.swap b d
  let z : Fin (n + 1) → Complex := fun j => sixVertexBethePhase (p j)
  let f : Fin (n + 1) → Complex := fun k =>
    sixVertexBetheWordEdgeFactor c z sigma w k
  let f' : Fin (n + 1) → Complex := fun k =>
    sixVertexBetheWordEdgeFactor c z sigma' w' k
  have hab : a ≠ b := by
    intro h
    have ha := (mem_sixVertexBetheMLBoundarySet w a).mp (by simp [hML])
    apply ha.1
    rw [h, show b = i.castSucc by rfl]
    exact hiL
  have hbd : b ≠ d := by
    intro h
    have := congrArg Fin.val h
    simp [b, d] at this
  have hfb : f b = sixVertexBetheL c (z (sigma d)) := by
    have hrotd : finRotate (n + 1) b = d := by
      apply Fin.ext
      simp [b, d]
    simp [f, sixVertexBetheWordEdgeFactor, hiL, hsuccL, hrotd, b, d]
  have hfa' : f' a = sixVertexBetheM c (z (sigma a)) := by
    have haM := (mem_sixVertexBetheMLBoundarySet w a).mp (by simp [hML]) |>.1
    have haM' : a ∉ w' := by simp [w', haM, hab]
    have hbM' : b ∉ w' := by simp [w']
    have had : a ≠ d := by
      intro h
      apply haM
      rw [h, show d = i.succ by rfl]
      exact hsuccL
    have hsigma'a : sigma' a = sigma a := by
      dsimp [sigma']
      rw [Equiv.swap_apply_of_ne_of_ne hab had]
    have harot : finRotate (n + 1) a = b := by exact hrot
    unfold f' sixVertexBetheWordEdgeFactor
    rw [if_neg haM']
    rw [if_neg (by rw [hrot]; exact hbM')]
    rw [hsigma'a]
  have hrest :
      (∏ k ∈ ((Finset.univ.erase a).erase b), f' k) =
        ∏ k ∈ ((Finset.univ.erase a).erase b), f k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hka : k ≠ a := by simpa using (Finset.mem_erase.mp
      (Finset.mem_erase.mp hk).2).1
    have hkb : k ≠ b := (Finset.mem_erase.mp hk).1
    have hrotb : finRotate (n + 1) k ≠ b := by
      intro h
      apply hka
      exact (finRotate (n + 1)).injective (h.trans hrot.symm)
    have hrotd : finRotate (n + 1) k ≠ d := by
      intro h
      apply hkb
      apply (finRotate (n + 1)).injective
      rw [h]
      apply Fin.ext
      simp [b, d]
    have hmem : k ∈ w' ↔ k ∈ w := by simp [w', hkb]
    have hrotmem : finRotate (n + 1) k ∈ w' ↔
        finRotate (n + 1) k ∈ w := by
      constructor
      · intro h
        exact (Finset.mem_erase.mp h).2
      · intro h
        exact Finset.mem_erase.mpr ⟨hrotb, h⟩
    have hrotb' : k + 1 ≠ b := by
      simpa [finRotate_apply] using hrotb
    have hrotd' : k + 1 ≠ d := by
      simpa [finRotate_apply] using hrotd
    by_cases hkw : k ∈ w
    · by_cases hrw : finRotate (n + 1) k ∈ w
      · have hkw' : k ∈ w' := hmem.2 hkw
        have hrw' : finRotate (n + 1) k ∈ w' := hrotmem.2 hrw
        have hsrot : sigma' (finRotate (n + 1) k) =
            sigma (finRotate (n + 1) k) := by
          dsimp [sigma']
          rw [Equiv.swap_apply_of_ne_of_ne hrotb hrotd]
        unfold f f' sixVertexBetheWordEdgeFactor
        rw [if_pos hkw', if_pos hrw', if_pos hkw, if_pos hrw, hsrot]
      · have hkw' : k ∈ w' := hmem.2 hkw
        have hrw' : finRotate (n + 1) k ∉ w' := fun h =>
          hrw (hrotmem.1 h)
        unfold f f' sixVertexBetheWordEdgeFactor
        rw [if_pos hkw', if_neg hrw', if_pos hkw, if_neg hrw]
    · by_cases hrw : finRotate (n + 1) k ∈ w
      · have hkBound : k ∈ sixVertexBetheMLBoundarySet w :=
          (mem_sixVertexBetheMLBoundarySet w k).2 ⟨hkw, hrw⟩
        have hkeq : k = a := by simpa [hML] using hkBound
        exact (hka hkeq).elim
      · have hkd : k ≠ d := fun h => hkw (h.symm ▸ hsuccL)
        have hkw' : k ∉ w' := fun h => hkw (hmem.1 h)
        have hrw' : finRotate (n + 1) k ∉ w' := fun h =>
          hrw (hrotmem.1 h)
        have hsk : sigma' k = sigma k := by
          dsimp [sigma']
          rw [Equiv.swap_apply_of_ne_of_ne hkb hkd]
        unfold f f' sixVertexBetheWordEdgeFactor
        rw [if_neg hkw', if_neg hrw', if_neg hkw, if_neg hrw, hsk]
  have hold : sixVertexBetheWordCoefficientRemainder c z sigma w a =
      f b * ∏ k ∈ ((Finset.univ.erase a).erase b), f k := by
    unfold sixVertexBetheWordCoefficientRemainder
    change (∏ k ∈ Finset.univ.erase a, f k) = _
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) f
      (a := b) (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  have hnew : sixVertexBetheWordCoefficientRemainder c z sigma' w' b =
      f' a * ∏ k ∈ ((Finset.univ.erase a).erase b), f' k := by
    unfold sixVertexBetheWordCoefficientRemainder
    change (∏ k ∈ Finset.univ.erase b, f' k) = _
    rw [← Finset.mul_prod_erase (Finset.univ.erase b) f'
      (a := a) (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)]
    have herase : (Finset.univ.erase b).erase a =
        (Finset.univ.erase a).erase b := by
      ext k
      simp [and_left_comm, and_comm]
    rw [herase]
  unfold sixVertexBetheZeroHatCoefficient
  change sixVertexBetheM c (z (sigma' b)) *
      sixVertexBetheWordCoefficientRemainder c z sigma' w' b *
        sixVertexBetheL c (z (sigma d)) =
    sixVertexBetheM c (z (sigma a)) *
      sixVertexBetheWordCoefficientRemainder c z sigma w a *
        sixVertexBetheM c (z (sigma d))
  have hsigmab : sigma' b = sigma d := by
    simp [sigma', b, d, Equiv.Perm.mul_apply]
  rw [hsigmab, hold, hnew, hfb, hfa', hrest]
  ring


theorem sixVertexBetheZeroHatTerm_zip_adjacent
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 1) → Real) (ell : Fin (n + 1)) (hell : p ell = 0)
    (sigma : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) (a : Fin (n + 1)) (i : Fin n)
    (hrot : finRotate (n + 1) a = i.castSucc)
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (hiL : i.castSucc ∈ w) (hsuccL : i.succ ∈ w)
    (hzero : sigma i.castSucc = ell)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    sixVertexBetheZeroHatTerm (N := N) c p sigma x w a =
      sixVertexBetheZeroHatTerm (N := N) c p
        (sigma * Equiv.swap i.castSucc i.succ) x
        (w.erase i.castSucc) i.castSucc := by
  let b : Fin (n + 1) := i.castSucc
  let d : Fin (n + 1) := i.succ
  let sigma' := sigma * Equiv.swap b d
  let w' := w.erase b
  have hbd : b ≠ d := by
    intro h
    have := congrArg Fin.val h
    simp [b, d] at this
  have hright : sigma d ≠ ell := by
    intro h
    exact hbd (sigma.injective (hzero.trans h.symm))
  have hphase : sixVertexBethePhase (p (sigma d)) ≠ 1 :=
    hother _ hright
  have hM := sixVertexBetheM_phase_ne_zero hc (p (sigma d))
  have hL := sixVertexBetheL_phase_ne_zero hc (p (sigma d))
  have hamp0 := sixVertexBetheAmplitude_adjacent_exchange hc p sigma i
  rw [hzero, hell] at hamp0
  have hamp : sixVertexBetheM c (sixVertexBethePhase (p (sigma d))) *
      sixVertexBetheAmplitude c p sigma' =
      sixVertexBetheL c (sixVertexBethePhase (p (sigma d))) *
        sixVertexBetheAmplitude c p sigma := by
    have hE := sixVertexTheta_zero_exp_neg_eq_neg_M_div_L hc hphase
    change Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma d))) *
        sixVertexBetheAmplitude c p sigma' =
      -sixVertexBetheAmplitude c p sigma at hamp0
    rw [hE] at hamp0
    field_simp [hL] at hamp0
    linear_combination -hamp0
  have hcoef := sixVertexBetheZeroHatCoefficient_zip_adjacent
    hc p sigma w a i hrot hML hiL hsuccL
  have hmono := sixVertexBetheWordMonomial_erase_zero_zip_adjacent
    (N := N) p ell hell sigma x w i hiL hsuccL hzero
  have hAC : sixVertexBetheAmplitude c p sigma *
      sixVertexBetheZeroHatCoefficient c p sigma w a =
      sixVertexBetheAmplitude c p sigma' *
        sixVertexBetheZeroHatCoefficient c p sigma' w' b := by
    apply mul_left_cancel₀ (mul_ne_zero hM hL)
    calc
      _ = (sixVertexBetheL c (sixVertexBethePhase (p (sigma d))) *
          sixVertexBetheAmplitude c p sigma) *
        (sixVertexBetheZeroHatCoefficient c p sigma w a *
          sixVertexBetheM c (sixVertexBethePhase (p (sigma d)))) := by ring
      _ = (sixVertexBetheM c (sixVertexBethePhase (p (sigma d))) *
          sixVertexBetheAmplitude c p sigma') *
        (sixVertexBetheZeroHatCoefficient c p sigma' w' b *
          sixVertexBetheL c (sixVertexBethePhase (p (sigma d)))) := by
            rw [hamp, hcoef]
      _ = _ := by ring
  unfold sixVertexBetheZeroHatTerm
  change sixVertexBetheAmplitude c p sigma *
      sixVertexBetheZeroHatCoefficient c p sigma w a *
        sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
          sigma x w =
    sixVertexBetheAmplitude c p sigma' *
      sixVertexBetheZeroHatCoefficient c p sigma' w' b *
        sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
          sigma' x w'
  rw [hmono, hAC]

theorem sixVertexBetheMLBoundarySet_nonempty_of_nonempty_ne_univ
    {n : Nat} (w : Finset (Fin (n + 1)))
    (hne : w ≠ ∅) (hnu : w ≠ Finset.univ) :
    (sixVertexBetheMLBoundarySet w).Nonempty := by
  rcases exists_sixVertexBetheCyclic_ML_of_nonconstant w hne hnu with
    ⟨i, hiM, hiL⟩ | ⟨hlast, hzero⟩
  · exact ⟨i.castSucc,
      (mem_sixVertexBetheMLBoundarySet w i.castSucc).2
        ⟨hiM, by
          simpa [show finRotate (n + 1) i.castSucc = i.succ by
            apply Fin.ext
            simp] using hiL⟩⟩
  · exact ⟨Fin.last n,
      (mem_sixVertexBetheMLBoundarySet w (Fin.last n)).2
        ⟨hlast, by simpa using hzero⟩⟩

theorem sixVertexBetheMLBoundarySet_erase_first
    {n : Nat} (w : Finset (Fin (n + 1))) (a : Fin (n + 1))
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (hdL : finRotate (n + 1) (finRotate (n + 1) a) ∈ w) :
    sixVertexBetheMLBoundarySet
        (w.erase (finRotate (n + 1) a)) =
      {finRotate (n + 1) a} := by
  let b := finRotate (n + 1) a
  let d := finRotate (n + 1) b
  have haBound : a ∈ sixVertexBetheMLBoundarySet w := by simp [hML]
  have haML := (mem_sixVertexBetheMLBoundarySet w a).mp haBound
  have hdL' : d ∈ w := by simpa [b, d] using hdL
  ext k
  simp only [mem_sixVertexBetheMLBoundarySet, Finset.mem_singleton]
  constructor
  · intro hk
    have hkM : k ∉ w.erase b := hk.1
    have hkrotL : finRotate (n + 1) k ∈ w.erase b := hk.2
    have hkrotLw : finRotate (n + 1) k ∈ w := (Finset.mem_erase.mp hkrotL).2
    by_cases hkb : k = b
    · exact hkb
    · have hkM' : k ∉ w := by
        intro hkw
        exact hkM (Finset.mem_erase.mpr ⟨hkb, hkw⟩)
      have hkBound : k ∈ sixVertexBetheMLBoundarySet w :=
        (mem_sixVertexBetheMLBoundarySet w k).2 ⟨hkM', hkrotLw⟩
      have hka : k = a := by simpa [hML] using hkBound
      subst k
      exact False.elim ((Finset.mem_erase.mp hkrotL).1 rfl)
  · rintro rfl
    have hdb : d ≠ b := by
      intro h
      have hrotEq : finRotate (n + 1) b = finRotate (n + 1) a := by
        simpa [b, d] using h
      have hba : b = a := (finRotate (n + 1)).injective hrotEq
      exact haML.1 (hba ▸ haML.2)
    exact ⟨by simp, Finset.mem_erase.mpr ⟨hdb, hdL'⟩⟩

theorem sixVertexBethe_erase_first_eq_empty_of_next_not_mem
    {n : Nat} (w : Finset (Fin (n + 1))) (a : Fin (n + 1))
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (hdM : finRotate (n + 1) (finRotate (n + 1) a) ∉ w) :
    w.erase (finRotate (n + 1) a) = ∅ := by
  let b := finRotate (n + 1) a
  let u := w.erase b
  have huNotUniv : u ≠ Finset.univ := by
    intro h
    have : finRotate (n + 1) b ∈ u := by rw [h]; simp
    exact hdM (by simpa [u, b] using (Finset.mem_erase.mp this).2)
  by_contra hu
  have hnon := sixVertexBetheMLBoundarySet_nonempty_of_nonempty_ne_univ
    u hu huNotUniv
  obtain ⟨k, hk⟩ := hnon
  have hkML := (mem_sixVertexBetheMLBoundarySet u k).mp hk
  have hkrot : finRotate (n + 1) k ∈ w :=
    (Finset.mem_erase.mp hkML.2).2
  have hkb : k ≠ b := by
    intro h
    subst k
    exact hdM hkrot
  have hkM : k ∉ w := by
    intro hkw
    exact hkML.1 (Finset.mem_erase.mpr ⟨hkb, hkw⟩)
  have hkBound : k ∈ sixVertexBetheMLBoundarySet w :=
    (mem_sixVertexBetheMLBoundarySet w k).2 ⟨hkM, hkrot⟩
  have hka : k = a := by simpa [hML] using hkBound
  subst k
  exact (Finset.mem_erase.mp hkML.2).1 rfl

theorem sixVertexBetheZeroHatCoefficient_zip_boundary
    {c : Real} {n : Nat} (p : Fin (n + 2) → Real)
    (sigma : Equiv.Perm (Fin (n + 2))) (w : Finset (Fin (n + 2)))
    (a : Fin (n + 2)) (hrot : finRotate (n + 2) a = Fin.last (n + 1))
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (hlastL : Fin.last (n + 1) ∈ w) (hzeroL : (0 : Fin (n + 2)) ∈ w) :
    sixVertexBetheZeroHatCoefficient c p
        (sigma * Equiv.swap (Fin.last (n + 1)) 0)
        (w.erase (Fin.last (n + 1))) (Fin.last (n + 1)) *
        sixVertexBetheL c (sixVertexBethePhase (p (sigma 0))) =
      sixVertexBetheZeroHatCoefficient c p sigma w a *
        sixVertexBetheM c (sixVertexBethePhase (p (sigma 0))) := by
  let b : Fin (n + 2) := Fin.last (n + 1)
  let d : Fin (n + 2) := 0
  let w' := w.erase b
  let sigma' := sigma * Equiv.swap b d
  let z : Fin (n + 2) → Complex := fun j => sixVertexBethePhase (p j)
  let f : Fin (n + 2) → Complex := fun k =>
    sixVertexBetheWordEdgeFactor c z sigma w k
  let f' : Fin (n + 2) → Complex := fun k =>
    sixVertexBetheWordEdgeFactor c z sigma' w' k
  have hab : a ≠ b := by
    intro h
    have ha := (mem_sixVertexBetheMLBoundarySet w a).mp (by simp [hML])
    exact ha.1 (h ▸ hlastL)
  have hbd : b ≠ d := by simp [b, d]
  have hrotd : finRotate (n + 2) b = d := by
    apply Fin.ext
    simp [b, d]
  have hfb : f b = sixVertexBetheL c (z (sigma d)) := by
    simp [f, sixVertexBetheWordEdgeFactor, hlastL, hzeroL, hrotd, b, d]
  have hfa' : f' a = sixVertexBetheM c (z (sigma a)) := by
    have haM := (mem_sixVertexBetheMLBoundarySet w a).mp (by simp [hML]) |>.1
    have haM' : a ∉ w' := by simp [w', haM, hab]
    have hbM' : b ∉ w' := by simp [w']
    have had : a ≠ d := fun h => haM (h ▸ hzeroL)
    have hsigma'a : sigma' a = sigma a := by
      dsimp [sigma']
      rw [Equiv.swap_apply_of_ne_of_ne hab had]
    unfold f' sixVertexBetheWordEdgeFactor
    rw [if_neg haM', if_neg (by rw [hrot]; exact hbM'), hsigma'a]
  have hrest :
      (∏ k ∈ ((Finset.univ.erase a).erase b), f' k) =
        ∏ k ∈ ((Finset.univ.erase a).erase b), f k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hka : k ≠ a := by simpa using (Finset.mem_erase.mp
      (Finset.mem_erase.mp hk).2).1
    have hkb : k ≠ b := (Finset.mem_erase.mp hk).1
    have hrotb : finRotate (n + 2) k ≠ b := by
      intro h
      exact hka ((finRotate (n + 2)).injective (h.trans hrot.symm))
    have hrotd' : finRotate (n + 2) k ≠ d := by
      intro h
      exact hkb ((finRotate (n + 2)).injective (h.trans hrotd.symm))
    have hmem : k ∈ w' ↔ k ∈ w := by simp [w', hkb]
    have hrotmem : finRotate (n + 2) k ∈ w' ↔
        finRotate (n + 2) k ∈ w := by
      constructor
      · exact fun h => (Finset.mem_erase.mp h).2
      · exact fun h => Finset.mem_erase.mpr ⟨hrotb, h⟩
    by_cases hkw : k ∈ w
    · by_cases hrw : finRotate (n + 2) k ∈ w
      · have hkw' := hmem.2 hkw
        have hrw' := hrotmem.2 hrw
        have hsrot : sigma' (finRotate (n + 2) k) =
            sigma (finRotate (n + 2) k) := by
          dsimp [sigma']
          rw [Equiv.swap_apply_of_ne_of_ne hrotb hrotd']
        unfold f f' sixVertexBetheWordEdgeFactor
        rw [if_pos hkw', if_pos hrw', if_pos hkw, if_pos hrw, hsrot]
      · have hkw' := hmem.2 hkw
        have hrw' : finRotate (n + 2) k ∉ w' := fun h => hrw (hrotmem.1 h)
        unfold f f' sixVertexBetheWordEdgeFactor
        rw [if_pos hkw', if_neg hrw', if_pos hkw, if_neg hrw]
    · by_cases hrw : finRotate (n + 2) k ∈ w
      · have hkBound : k ∈ sixVertexBetheMLBoundarySet w :=
          (mem_sixVertexBetheMLBoundarySet w k).2 ⟨hkw, hrw⟩
        have hkeq : k = a := by simpa [hML] using hkBound
        exact (hka hkeq).elim
      · have hkd : k ≠ d := fun h => hkw (h ▸ hzeroL)
        have hkw' : k ∉ w' := fun h => hkw (hmem.1 h)
        have hrw' : finRotate (n + 2) k ∉ w' := fun h => hrw (hrotmem.1 h)
        have hsk : sigma' k = sigma k := by
          dsimp [sigma']
          rw [Equiv.swap_apply_of_ne_of_ne hkb hkd]
        unfold f f' sixVertexBetheWordEdgeFactor
        rw [if_neg hkw', if_neg hrw', if_neg hkw, if_neg hrw, hsk]
  have hold : sixVertexBetheWordCoefficientRemainder c z sigma w a =
      f b * ∏ k ∈ ((Finset.univ.erase a).erase b), f k := by
    unfold sixVertexBetheWordCoefficientRemainder
    change (∏ k ∈ Finset.univ.erase a, f k) = _
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) f
      (a := b) (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  have hnew : sixVertexBetheWordCoefficientRemainder c z sigma' w' b =
      f' a * ∏ k ∈ ((Finset.univ.erase a).erase b), f' k := by
    unfold sixVertexBetheWordCoefficientRemainder
    change (∏ k ∈ Finset.univ.erase b, f' k) = _
    rw [← Finset.mul_prod_erase (Finset.univ.erase b) f'
      (a := a) (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)]
    have herase : (Finset.univ.erase b).erase a =
        (Finset.univ.erase a).erase b := by
      ext k
      simp [and_comm]
    rw [herase]
  unfold sixVertexBetheZeroHatCoefficient
  change sixVertexBetheM c (z (sigma' b)) *
      sixVertexBetheWordCoefficientRemainder c z sigma' w' b *
        sixVertexBetheL c (z (sigma d)) =
    sixVertexBetheM c (z (sigma a)) *
      sixVertexBetheWordCoefficientRemainder c z sigma w a *
        sixVertexBetheM c (z (sigma d))
  have hsigmab : sigma' b = sigma d := by simp [sigma', b, d]
  rw [hsigmab, hold, hnew, hfb, hfa', hrest]
  ring

theorem sixVertexBetheWordMonomial_erase_zero_zip_boundary
    {N n : Nat} (p : Fin (n + 2) → Real) (ell : Fin (n + 2))
    (hell : p ell = 0) (sigma : Equiv.Perm (Fin (n + 2)))
    (x : Fin (n + 2) → Int) (w : Finset (Fin (n + 2)))
    (hlastL : Fin.last (n + 1) ∈ w) (hzeroL : (0 : Fin (n + 2)) ∈ w)
    (hroot : sigma (Fin.last (n + 1)) = ell) :
    sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
        (sigma * Equiv.swap (Fin.last (n + 1)) 0) x
        (w.erase (Fin.last (n + 1))) =
      sixVertexBethePhase (p (sigma 0)) ^ N *
        sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
          sigma x w := by
  let w' := w.erase (Fin.last (n + 1))
  let z : Fin (n + 2) → Complex := fun j => sixVertexBethePhase (p j)
  have hlastM' : Fin.last (n + 1) ∉ w' := by simp [w']
  have hzeroL' : (0 : Fin (n + 2)) ∈ w' := by
    simp [w', hzeroL]
  have hcov := sixVertexBetheWordMonomial_boundary_covariant (N := N)
    z (fun j => Complex.exp_ne_zero _) sigma x w' hlastM' hzeroL'
  have hphaseLast : z (sigma (Fin.last (n + 1))) = 1 := by
    simp [z, hroot, hell, sixVertexBethePhase]
  rw [hphaseLast, one_pow, one_mul] at hcov
  have herase : sixVertexBetheWordMonomial N z sigma x w' =
      sixVertexBetheWordMonomial N z sigma x w := by
    unfold sixVertexBetheWordMonomial
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hkLast : k = Fin.last (n + 1)
    · subst k
      simp [w', hlastL, hroot, hell, z, sixVertexBethePhase]
    · simp [w', hkLast]
  rw [herase] at hcov
  exact hcov

theorem sixVertexBetheZeroHatTerm_zip_boundary
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (sigma : Equiv.Perm (Fin (n + 2))) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2))) (a : Fin (n + 2))
    (hrot : finRotate (n + 2) a = Fin.last (n + 1))
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (hlastL : Fin.last (n + 1) ∈ w) (hzeroL : (0 : Fin (n + 2)) ∈ w)
    (hroot : sigma (Fin.last (n + 1)) = ell)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    sixVertexBetheZeroHatTerm (N := N) c p sigma x w a =
      sixVertexBetheZeroHatTerm (N := N) c p
        (sigma * Equiv.swap (Fin.last (n + 1)) 0) x
        (w.erase (Fin.last (n + 1))) (Fin.last (n + 1)) := by
  let b : Fin (n + 2) := Fin.last (n + 1)
  let d : Fin (n + 2) := 0
  let sigma' := sigma * Equiv.swap b d
  let w' := w.erase b
  have hbd : b ≠ d := by simp [b, d]
  have hright : sigma d ≠ ell := by
    intro h
    exact hbd (sigma.injective (hroot.trans h.symm))
  have hphase := hother _ hright
  have hM := sixVertexBetheM_phase_ne_zero hc (p (sigma d))
  have hL := sixVertexBetheL_phase_ne_zero hc (p (sigma d))
  have hamp0 := hp.amplitude_boundary_exchange hc sigma
  rw [hroot, hell] at hamp0
  rw [sixVertexBetheBoundaryPermutation_eq_swap n] at hamp0
  rw [show sixVertexBethePhase 0 = 1 by simp [sixVertexBethePhase],
    one_pow, one_mul] at hamp0
  have hamp : sixVertexBetheM c (sixVertexBethePhase (p (sigma d))) *
      (sixVertexBethePhase (p (sigma d)) ^ N *
        sixVertexBetheAmplitude c p sigma') =
      sixVertexBetheL c (sixVertexBethePhase (p (sigma d))) *
        sixVertexBetheAmplitude c p sigma := by
    have hE := sixVertexTheta_zero_exp_neg_eq_neg_M_div_L hc hphase
    dsimp only [d, sigma']
    change Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma d))) *
        sixVertexBethePhase (p (sigma d)) ^ N *
          sixVertexBetheAmplitude c p sigma' =
      -sixVertexBetheAmplitude c p sigma at hamp0
    rw [hE] at hamp0
    field_simp [hL] at hamp0
    linear_combination -hamp0
  have hcoef := sixVertexBetheZeroHatCoefficient_zip_boundary
    (c := c) p sigma w a hrot hML hlastL hzeroL
  have hmono := sixVertexBetheWordMonomial_erase_zero_zip_boundary
    (N := N) p ell hell sigma x w hlastL hzeroL hroot
  have hAC : sixVertexBetheAmplitude c p sigma *
      sixVertexBetheZeroHatCoefficient c p sigma w a =
      (sixVertexBethePhase (p (sigma d)) ^ N *
        sixVertexBetheAmplitude c p sigma') *
        sixVertexBetheZeroHatCoefficient c p sigma' w' b := by
    apply mul_left_cancel₀ (mul_ne_zero hM hL)
    calc
      _ = (sixVertexBetheL c (sixVertexBethePhase (p (sigma d))) *
            sixVertexBetheAmplitude c p sigma) *
          (sixVertexBetheZeroHatCoefficient c p sigma w a *
            sixVertexBetheM c (sixVertexBethePhase (p (sigma d)))) := by ring
      _ = (sixVertexBetheM c (sixVertexBethePhase (p (sigma d))) *
            (sixVertexBethePhase (p (sigma d)) ^ N *
              sixVertexBetheAmplitude c p sigma')) *
          (sixVertexBetheZeroHatCoefficient c p sigma' w' b *
            sixVertexBetheL c (sixVertexBethePhase (p (sigma d)))) := by
              rw [hamp, hcoef]
      _ = _ := by ring
  unfold sixVertexBetheZeroHatTerm
  change sixVertexBetheAmplitude c p sigma *
      sixVertexBetheZeroHatCoefficient c p sigma w a *
        sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
          sigma x w =
    sixVertexBetheAmplitude c p sigma' *
      sixVertexBetheZeroHatCoefficient c p sigma' w' b *
        sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j))
          sigma' x w'
  rw [hmono, hAC]
  ring

theorem sixVertexBetheZeroHatTerm_singleton
    {c : Real} {N n : Nat} (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (sigma : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → Int)
    (a s : Fin (n + 1)) (hrot : finRotate (n + 1) a = s)
    (has : a ≠ s) (hroot : sigma s = ell) :
    sixVertexBetheZeroHatTerm (N := N) c p sigma x {s} a =
      (∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheM c (sixVertexBethePhase (p j))) *
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial p sigma x := by
  let z : Fin (n + 1) → Complex := fun j => sixVertexBethePhase (p j)
  have hphaseS : z (sigma s) = 1 := by
    simp [z, hroot, hell, sixVertexBethePhase]
  have hcoeff : sixVertexBetheZeroHatCoefficient c p sigma {s} a =
      ∏ k, sixVertexBetheM c (z (sigma k)) := by
    unfold sixVertexBetheZeroHatCoefficient
      sixVertexBetheWordCoefficientRemainder
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => sixVertexBetheM c (z (sigma k))) (Finset.mem_univ a)]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    have hka : k ≠ a := (Finset.mem_erase.mp hk).1
    unfold sixVertexBetheWordEdgeFactor
    by_cases hks : k = s
    · subst k
      have hrots : finRotate (n + 1) s ≠ s := by
        intro h
        apply has
        exact (finRotate (n + 1)).injective (hrot.trans h.symm)
      rw [if_pos (by simp), if_neg (by simpa using hrots)]
      rw [hphaseS]
      simp [sixVertexBetheM]
    · have hrotks : finRotate (n + 1) k ≠ s := by
        intro h
        apply hka
        exact (finRotate (n + 1)).injective (h.trans hrot.symm)
      rw [if_neg (by simpa using hks), if_neg (by simpa using hrotks)]
  have hprod : (∏ k, sixVertexBetheM c (z (sigma k))) =
      ∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheM c (sixVertexBethePhase (p j)) := by
    rw [Equiv.prod_comp sigma
      (fun j => sixVertexBetheM c (sixVertexBethePhase (p j)))]
    rw [← Finset.prod_erase_mul Finset.univ
      (fun j => sixVertexBetheM c (sixVertexBethePhase (p j)))
      (Finset.mem_univ ell)]
    rw [hell]
    simp [sixVertexBethePhase, sixVertexBetheM]
  have hmono : sixVertexBetheWordMonomial N z sigma x {s} =
      sixVertexBetheIntMonomial p sigma x := by
    unfold sixVertexBetheWordMonomial sixVertexBetheIntMonomial
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hks : k = s
    · subst k
      rw [if_pos (Finset.mem_singleton_self s), hphaseS]
      simp [hroot, hell, sixVertexBethePhase]
    · simp [hks, z]
  unfold sixVertexBetheZeroHatTerm
  rw [hcoeff, hprod, hmono]
  ring


theorem sixVertexBetheZeroHatTerm_normalize
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (sigma : Equiv.Perm (Fin (n + 2))) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2))) (a : Fin (n + 2))
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (hroot : sigma (finRotate (n + 2) a) = ell)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    ∃ t, ∃ rho : Equiv.Perm (Fin (n + 2)),
      t ∈ w ∧ rho t = ell ∧
      (∀ k, k ∉ w → rho k = sigma k) ∧
      sixVertexBetheZeroHatTerm (N := N) c p sigma x w a =
        (∏ j ∈ (Finset.univ.erase ell),
          sixVertexBetheM c (sixVertexBethePhase (p j))) *
          sixVertexBetheAmplitude c p rho *
            sixVertexBetheIntMonomial p rho x := by
  classical
  induction hcard : w.card using Nat.strong_induction_on generalizing w a sigma with
  | h m ih =>
      let b := finRotate (n + 2) a
      let d := finRotate (n + 2) b
      have haBound : a ∈ sixVertexBetheMLBoundarySet w := by simp [hML]
      have haML := (mem_sixVertexBetheMLBoundarySet w a).mp haBound
      have hbL : b ∈ w := by simpa [b] using haML.2
      have hab : a ≠ b := by
        intro h
        exact haML.1 (h.symm ▸ hbL)
      by_cases hdL : d ∈ w
      · let w' := w.erase b
        let sigma' := sigma * Equiv.swap b d
        have hbd : b ≠ d := by
          intro h
          have hba : b = a := (finRotate (n + 2)).injective
            (by simpa [b, d] using h)
          exact hab hba.symm
        have hML' : sixVertexBetheMLBoundarySet w' = {b} := by
          simpa [w', b, d] using
            sixVertexBetheMLBoundarySet_erase_first w a hML
              (by simpa [b, d] using hdL)
        have hroot' : sigma' (finRotate (n + 2) b) = ell := by
          change sigma' d = ell
          have : sigma' d = sigma b := by
            simp [sigma', Equiv.Perm.mul_apply, hbd]
          rw [this]
          simpa [b, finRotate_apply] using hroot
        have hcard' : w'.card < m := by
          rw [← hcard]
          rw [show w'.card = w.card - 1 by
            exact Finset.card_erase_of_mem hbL]
          have : 0 < w.card := Finset.card_pos.mpr ⟨b, hbL⟩
          omega
        obtain ⟨t, rho, htw', hrho, hout, hterm⟩ :=
          ih w'.card hcard' sigma' w' b hML' hroot' rfl
        have hzip : sixVertexBetheZeroHatTerm (N := N) c p sigma x w a =
            sixVertexBetheZeroHatTerm (N := N) c p sigma' x w' b := by
          by_cases hbLast : b = Fin.last (n + 1)
          · have hdZero : d = 0 := by
              apply Fin.ext
              simp [d, hbLast]
            have hrotLast : finRotate (n + 2) a = Fin.last (n + 1) := by
              simpa [b] using hbLast
            have hlastL : Fin.last (n + 1) ∈ w := by
              rw [← hbLast]
              exact hbL
            have hzeroL : (0 : Fin (n + 2)) ∈ w := by
              rw [← hdZero]
              exact hdL
            have hrootLast : sigma (Fin.last (n + 1)) = ell := by
              rw [← hbLast]
              simpa [b] using hroot
            simpa [sigma', w', hbLast, hdZero] using
              sixVertexBetheZeroHatTerm_zip_boundary hc p hp ell hell sigma x w a
                hrotLast hML hlastL hzeroL hrootLast hother
          · have hbval : b.val < n + 1 := by
              have hle : b.val ≤ n + 1 := by omega
              have hne : b.val ≠ n + 1 := by
                intro h
                apply hbLast
                apply Fin.ext
                simpa using h
              omega
            let i : Fin (n + 1) := ⟨b.val, hbval⟩
            have hib : i.castSucc = b := by apply Fin.ext; rfl
            have hid : i.succ = d := by
              apply Fin.ext
              rw [show d = finRotate (n + 2) b by rfl,
                coe_finRotate_of_ne_last hbLast]
              rfl
            simpa [sigma', w', hib, hid] using
              sixVertexBetheZeroHatTerm_zip_adjacent hc p ell hell sigma x w a i
                (by simpa [b, hib] using rfl) hML
                (by simpa [hib] using hbL) (by simpa [hid] using hdL)
                (by simpa [hib, b] using hroot) hother
        refine ⟨t, rho, ?_, hrho, ?_, hzip.trans hterm⟩
        · exact (Finset.mem_erase.mp htw').2
        · intro k hkw
          have hkw' : k ∉ w' := fun hk => hkw (Finset.mem_erase.mp hk).2
          rw [hout k hkw']
          have hkb : k ≠ b := fun h => hkw (h ▸ hbL)
          have hkd : k ≠ d := fun h => hkw (h ▸ hdL)
          simp [sigma', Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne hkb hkd]
      · have herase := sixVertexBethe_erase_first_eq_empty_of_next_not_mem
          w a hML (by simpa [b, d] using hdL)
        have hw : w = {b} := by
          apply Finset.Subset.antisymm
          · intro k hkw
            by_contra hkb
            have hkb' : k ≠ b := by simpa using hkb
            have hk : k ∈ w.erase b := Finset.mem_erase.mpr ⟨hkb', hkw⟩
            rw [show w.erase b = ∅ by simpa [b] using herase] at hk
            simp at hk
          · intro k hk
            have hkb : k = b := by simpa using hk
            simpa [hkb] using hbL
        refine ⟨b, sigma, hbL, ?_, ?_, ?_⟩
        · simpa [b] using hroot
        · intro k hkw
          rfl
        · rw [hw]
          exact sixVertexBetheZeroHatTerm_singleton p ell hell sigma x a b
            (by simp [b]) hab (by simpa [b] using hroot)


theorem sixVertexBetheZeroHatTerm_normalize_mulRight
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (x : Fin (n + 2) → Int) (w : Finset (Fin (n + 2)))
    (a : Fin (n + 2)) (hML : sixVertexBetheMLBoundarySet w = {a})
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    ∃ t, ∃ tau : Equiv.Perm (Fin (n + 2)),
      t ∈ w ∧ finRotate (n + 2) t ∉ w ∧
      (∀ u, u ∈ w → finRotate (n + 2) u ∉ w → u = t) ∧
      tau t = finRotate (n + 2) a ∧
      (∀ k, k ∉ w → tau k = k) ∧
      ∀ sigma : Equiv.Perm (Fin (n + 2)),
        sigma (finRotate (n + 2) a) = ell →
        sixVertexBetheZeroHatTerm (N := N) c p sigma x w a =
          (∏ j ∈ (Finset.univ.erase ell),
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
            sixVertexBetheAmplitude c p (sigma * tau) *
              sixVertexBetheIntMonomial p (sigma * tau) x := by
  classical
  induction hcard : w.card using Nat.strong_induction_on generalizing w a with
  | h m ih =>
      let b := finRotate (n + 2) a
      let d := finRotate (n + 2) b
      have haBound : a ∈ sixVertexBetheMLBoundarySet w := by simp [hML]
      have haML := (mem_sixVertexBetheMLBoundarySet w a).mp haBound
      have hbL : b ∈ w := by simpa [b] using haML.2
      have hab : a ≠ b := by
        intro h
        exact haML.1 (h.symm ▸ hbL)
      by_cases hdL : d ∈ w
      · let w' := w.erase b
        have hbd : b ≠ d := by
          intro h
          have hba : b = a := (finRotate (n + 2)).injective
            (by simpa [b, d] using h)
          exact hab hba.symm
        have hML' : sixVertexBetheMLBoundarySet w' = {b} := by
          simpa [w', b, d] using
            sixVertexBetheMLBoundarySet_erase_first w a hML
              (by simpa [b, d] using hdL)
        have hcard' : w'.card < m := by
          rw [← hcard]
          rw [show w'.card = w.card - 1 by
            exact Finset.card_erase_of_mem hbL]
          have : 0 < w.card := Finset.card_pos.mpr ⟨b, hbL⟩
          omega
        obtain ⟨t, tau', htw', htEnd', htUnique', htau', hout', hterm'⟩ :=
          ih w'.card hcard' w' b hML' rfl
        let tau := Equiv.swap b d * tau'
        have htaut : tau t = b := by
          change Equiv.swap b d (tau' t) = b
          rw [htau']
          simp [d, hbd]
        have hout : ∀ k, k ∉ w → tau k = k := by
          intro k hkw
          have hkw' : k ∉ w' := fun hk => hkw (Finset.mem_erase.mp hk).2
          have hkb : k ≠ b := fun h => hkw (h ▸ hbL)
          have hkd : k ≠ d := fun h => hkw (h ▸ hdL)
          change Equiv.swap b d (tau' k) = k
          rw [hout' k hkw']
          exact Equiv.swap_apply_of_ne_of_ne hkb hkd
        have htEnd : finRotate (n + 2) t ∉ w := by
          intro htrot
          by_cases hrotb : finRotate (n + 2) t = b
          · have hta : t = a := (finRotate (n + 2)).injective
              (by simpa [b] using hrotb)
            exact haML.1 (hta ▸ (Finset.mem_erase.mp htw').2)
          · exact htEnd' (Finset.mem_erase.mpr ⟨hrotb, htrot⟩)
        have htUnique : ∀ u, u ∈ w → finRotate (n + 2) u ∉ w → u = t := by
          intro u huw huEnd
          have hub : u ≠ b := by
            intro h
            apply huEnd
            simpa [h, d] using hdL
          have huw' : u ∈ w' := Finset.mem_erase.mpr ⟨hub, huw⟩
          have huEnd' : finRotate (n + 2) u ∉ w' := fun h =>
            huEnd (Finset.mem_erase.mp h).2
          exact htUnique' u huw' huEnd'
        refine ⟨t, tau, (Finset.mem_erase.mp htw').2, htEnd, htUnique,
          by simpa [b] using htaut, hout, ?_⟩
        intro sigma hroot
        let sigma' := sigma * Equiv.swap b d
        have hroot' : sigma' (finRotate (n + 2) b) = ell := by
          change sigma' d = ell
          have : sigma' d = sigma b := by
            simp [sigma', Equiv.Perm.mul_apply, hbd]
          rw [this]
          simpa [b, finRotate_apply] using hroot
        have hzip : sixVertexBetheZeroHatTerm (N := N) c p sigma x w a =
            sixVertexBetheZeroHatTerm (N := N) c p sigma' x w' b := by
          by_cases hbLast : b = Fin.last (n + 1)
          · have hdZero : d = 0 := by
              apply Fin.ext
              simp [d, hbLast]
            have hrotLast : finRotate (n + 2) a = Fin.last (n + 1) := by
              simpa [b] using hbLast
            have hlastL : Fin.last (n + 1) ∈ w := by
              rw [← hbLast]
              exact hbL
            have hzeroL : (0 : Fin (n + 2)) ∈ w := by
              rw [← hdZero]
              exact hdL
            have hrootLast : sigma (Fin.last (n + 1)) = ell := by
              rw [← hbLast]
              simpa [b] using hroot
            simpa [sigma', w', hbLast, hdZero] using
              sixVertexBetheZeroHatTerm_zip_boundary hc p hp ell hell sigma x w a
                hrotLast hML hlastL hzeroL hrootLast hother
          · have hbval : b.val < n + 1 := by
              have hle : b.val ≤ n + 1 := by omega
              have hne : b.val ≠ n + 1 := by
                intro h
                apply hbLast
                apply Fin.ext
                simpa using h
              omega
            let i : Fin (n + 1) := ⟨b.val, hbval⟩
            have hib : i.castSucc = b := by apply Fin.ext; rfl
            have hid : i.succ = d := by
              apply Fin.ext
              rw [show d = finRotate (n + 2) b by rfl,
                coe_finRotate_of_ne_last hbLast]
              rfl
            simpa [sigma', w', hib, hid] using
              sixVertexBetheZeroHatTerm_zip_adjacent hc p ell hell sigma x w a i
                (by simpa [b, hib] using rfl) hML
                (by simpa [hib] using hbL) (by simpa [hid] using hdL)
                (by simpa [hib, b] using hroot) hother
        rw [hzip, hterm' sigma' hroot']
        congr 2 <;> simp [sigma', tau, mul_assoc]
      · have herase := sixVertexBethe_erase_first_eq_empty_of_next_not_mem
          w a hML (by simpa [b, d] using hdL)
        have hw : w = {b} := by
          apply Finset.Subset.antisymm
          · intro k hkw
            by_contra hkb
            have hkb' : k ≠ b := by simpa using hkb
            have hk : k ∈ w.erase b := Finset.mem_erase.mpr ⟨hkb', hkw⟩
            rw [show w.erase b = ∅ by simpa [b] using herase] at hk
            simp at hk
          · intro k hk
            have hkb : k = b := by simpa using hk
            simpa [hkb] using hbL
        refine ⟨b, Equiv.refl _, hbL, by simpa [d] using hdL, ?_,
          by simp [b], ?_, ?_⟩
        · intro u huw huEnd
          rw [hw] at huw
          simpa using huw
        · intro k hkw
          rfl
        · intro sigma hroot
          rw [hw]
          simpa using sixVertexBetheZeroHatTerm_singleton p ell hell sigma x a b
            (by simp [b]) hab (by simpa [b] using hroot)


theorem sum_sixVertexBetheZeroHatTerm_eq_terminal
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (x : Fin (n + 2) → Int) (w : Finset (Fin (n + 2)))
    (a : Fin (n + 2)) (hML : sixVertexBetheMLBoundarySet w = {a})
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (F : Fin (n + 2) → Complex) :
    ∃ t ∈ w,
      finRotate (n + 2) t ∉ w ∧
      (∑ sigma : Equiv.Perm (Fin (n + 2)) with
          sigma (finRotate (n + 2) a) = ell,
        F (sigma a) *
          sixVertexBetheZeroHatTerm (N := N) c p sigma x w a) =
        (∏ j ∈ (Finset.univ.erase ell),
          sixVertexBetheM c (sixVertexBethePhase (p j))) *
          ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell,
            F (rho a) * sixVertexBetheAmplitude c p rho *
              sixVertexBetheIntMonomial p rho x := by
  classical
  obtain ⟨t, tau, htw, htEnd, htUnique, htau, hout, hterm⟩ :=
    sixVertexBetheZeroHatTerm_normalize_mulRight hc p hp ell hell x w a hML hother
  have haM : a ∉ w :=
    ((mem_sixVertexBetheMLBoundarySet w a).mp (by simp [hML])).1
  have htaua : tau a = a := hout a haM
  let MP : Complex := ∏ j ∈ (Finset.univ.erase ell),
    sixVertexBetheM c (sixVertexBethePhase (p j))
  let G : Equiv.Perm (Fin (n + 2)) → Complex := fun rho =>
    if rho t = ell then
      F (rho a) * sixVertexBetheAmplitude c p rho *
        sixVertexBetheIntMonomial p rho x
    else 0
  have hreindex := (Equiv.sum_comp (Equiv.mulRight tau) G).symm
  refine ⟨t, htw, htEnd, ?_⟩
  rw [Finset.sum_filter, Finset.sum_filter]
  change (∑ sigma, if sigma (finRotate (n + 2) a) = ell then
      F (sigma a) * sixVertexBetheZeroHatTerm c p sigma x w a else 0) = _
  calc
    _ = MP * ∑ sigma, G (sigma * tau) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma hsigma
      by_cases hroot : sigma (finRotate (n + 2) a) = ell
      · rw [if_pos hroot, hterm sigma hroot]
        have hcond : (sigma * tau) t = ell := by
          change sigma (tau t) = ell
          rw [htau]
          exact hroot
        rw [show G (sigma * tau) =
            F ((sigma * tau) a) * sixVertexBetheAmplitude c p (sigma * tau) *
              sixVertexBetheIntMonomial p (sigma * tau) x by
          unfold G
          rw [if_pos hcond]]
        simp [htaua, MP, Equiv.Perm.mul_apply]
        ring
      · rw [if_neg hroot]
        have hcond : (sigma * tau) t ≠ ell := by
          change sigma (tau t) ≠ ell
          rw [htau]
          exact hroot
        rw [show G (sigma * tau) = 0 by
          unfold G
          rw [if_neg hcond]]
        simp
    _ = MP * ∑ rho, G rho := by
      congr 1
      simpa using hreindex.symm
    _ = _ := by rfl


end
end StatMech.FrontierD
