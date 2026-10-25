/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseConstant.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexBetheCyclicWord {m : Nat}
    (a t k : Fin (m + 1)) :
    k ∈ sixVertexBetheCyclicWord a t ↔
      0 < (k - a).val ∧ (k - a).val ≤ (t - a).val := by
  simp [sixVertexBetheCyclicWord]

theorem sixVertexBetheCyclicWord_MLBoundarySet
    {m : Nat} (a t : Fin (m + 1)) (hat : a ≠ t) :
    sixVertexBetheMLBoundarySet (sixVertexBetheCyclicWord a t) = {a} := by
  classical
  have hr0 : 0 < (t - a).val := by
    have hne : t - a ≠ 0 := sub_ne_zero.mpr hat.symm
    exact Fin.pos_iff_ne_zero.mpr hne
  have hm : 0 < m := by
    by_contra h
    have : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact hat ((Fin.eq_zero a).trans (Fin.eq_zero t).symm)
  ext k
  rw [mem_sixVertexBetheMLBoundarySet]
  simp only [Finset.mem_singleton]
  let q : Fin (m + 1) := k - a
  have hshift : finRotate (m + 1) k - a = q + 1 := by
    dsimp [q]
    rw [finRotate_apply]
    abel
  have hqval : ((q + 1 : Fin (m + 1)) : Nat) =
      if q = Fin.last m then 0 else q.val + 1 := by
    rw [← finRotate_apply]
    exact coe_finRotate q
  constructor
  · intro hk
    have hkM : ¬(0 < q.val ∧ q.val ≤ (t - a).val) := by
      simpa [q] using hk.1
    have hkL : 0 < (q + 1).val ∧
        (q + 1).val ≤ (t - a).val := by
      have h := (mem_sixVertexBetheCyclicWord a t
        (finRotate (m + 1) k)).mp hk.2
      rw [hshift] at h
      exact h
    have hqzero : q = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      by_cases hqlast : q = Fin.last m
      · rw [hqval, if_pos hqlast] at hkL
        omega
      · rw [hqval, if_neg hqlast] at hkL
        have hqle : q.val ≤ (t - a).val := by omega
        have hnpos : ¬ 0 < q.val := fun hpos => hkM ⟨hpos, hqle⟩
        omega
    apply sub_eq_zero.mp
    simpa [q] using hqzero
  · intro hka
    subst k
    constructor
    · simp
    · rw [mem_sixVertexBetheCyclicWord]
      have hshiftA : finRotate (m + 1) a - a = (1 : Fin (m + 1)) := by
        rw [finRotate_apply]
        abel
      rw [hshiftA]
      have hm1 : 1 < m + 1 := by omega
      constructor
      · change 0 < 1 % (m + 1)
        rw [Nat.mod_eq_of_lt hm1]
        omega
      · change 1 % (m + 1) ≤ (t - a).val
        rw [Nat.mod_eq_of_lt hm1]
        omega

theorem sixVertexBetheCyclicWord_unique_LM
    {m : Nat} (a t : Fin (m + 1)) (hat : a ≠ t) :
    t ∈ sixVertexBetheCyclicWord a t ∧
      finRotate (m + 1) t ∉ sixVertexBetheCyclicWord a t ∧
      ∀ u, u ∈ sixVertexBetheCyclicWord a t →
        finRotate (m + 1) u ∉ sixVertexBetheCyclicWord a t → u = t := by
  classical
  let r : Fin (m + 1) := t - a
  have hr0 : 0 < r.val := by
    exact Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr hat.symm)
  have hshift (k : Fin (m + 1)) :
      finRotate (m + 1) k - a = (k - a) + 1 := by
    rw [finRotate_apply]
    abel
  have hval (q : Fin (m + 1)) : ((q + 1 : Fin (m + 1)) : Nat) =
      if q = Fin.last m then 0 else q.val + 1 := by
    rw [← finRotate_apply]
    exact coe_finRotate q
  have htmem : t ∈ sixVertexBetheCyclicWord a t := by
    simp [r, hr0]
  have htend : finRotate (m + 1) t ∉ sixVertexBetheCyclicWord a t := by
    rw [mem_sixVertexBetheCyclicWord, hshift]
    intro h
    by_cases hrlast : r = Fin.last m
    · rw [hval, if_pos hrlast] at h
      omega
    · rw [hval, if_neg hrlast] at h
      omega
  refine ⟨htmem, htend, ?_⟩
  intro u humem huend
  let q : Fin (m + 1) := u - a
  have hq : 0 < q.val ∧ q.val ≤ r.val := by
    simpa [q, r] using (mem_sixVertexBetheCyclicWord a t u).mp humem
  have hnot : ¬(0 < (q + 1).val ∧ (q + 1).val ≤ r.val) := by
    intro h
    apply huend
    rw [mem_sixVertexBetheCyclicWord, hshift]
    simpa [q, r] using h
  have hqr : q = r := by
    apply Fin.ext
    by_cases hqlast : q = Fin.last m
    · have hrlast : r = Fin.last m := by
        apply Fin.ext
        simp only [Fin.val_last]
        have hqv : q.val = m := by simpa [hqlast]
        omega
      simpa [hqlast, hrlast]
    · rw [hval, if_neg hqlast] at hnot
      omega
  have hadd := congrArg (fun z : Fin (m + 1) => z + a) hqr
  simpa [q, r] using hadd

theorem eq_sixVertexBetheCyclicWord_of_boundaries
    {m : Nat} (w : Finset (Fin (m + 1))) (a t : Fin (m + 1))
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (htmem : t ∈ w) (htend : finRotate (m + 1) t ∉ w)
    (htUnique : ∀ u, u ∈ w → finRotate (m + 1) u ∉ w → u = t) :
    w = sixVertexBetheCyclicWord a t := by
  classical
  have haML := (mem_sixVertexBetheMLBoundarySet w a).mp (by simp [hML])
  have hat : a ≠ t := fun h => haML.1 (h ▸ htmem)
  let r : Fin (m + 1) := t - a
  have hr0 : 0 < r.val :=
    Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr hat.symm)
  have htform : a + r = t := by
    dsimp [r]
    abel
  have hstep (u : Fin (m + 1)) :
      finRotate (m + 1) u = u + 1 := finRotate_apply u
  have hinside : ∀ s : Nat, (hs0 : 0 < s) → (hsr : s ≤ r.val) →
      a + (⟨s, lt_of_le_of_lt hsr r.isLt⟩ : Fin (m + 1)) ∈ w := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro hs0 hsr
        by_cases hs1 : s = 1
        · subst s
          have : a + (1 : Fin (m + 1)) = finRotate (m + 1) a := by
            rw [finRotate_apply]
          have hfin : (⟨1, lt_of_le_of_lt hsr r.isLt⟩ : Fin (m + 1)) = 1 := by
            apply Fin.ext
            change 1 = 1 % (m + 1)
            rw [Nat.mod_eq_of_lt (by omega)]
          rw [hfin, this]
          exact haML.2
        · have hs2 : 0 < s - 1 := by omega
          have hpredr : s - 1 ≤ r.val := by omega
          let sp : Fin (m + 1) := ⟨s - 1, lt_of_le_of_lt hpredr r.isLt⟩
          let ss : Fin (m + 1) := ⟨s, lt_of_le_of_lt hsr r.isLt⟩
          have hpred : a + sp ∈ w := ih (s - 1) (by omega) hs2 hpredr
          have hpred_ne : a + sp ≠ t := by
            intro heq
            have heq' := congrArg (fun z : Fin (m + 1) => z - a) heq
            have hsval := congrArg Fin.val heq'
            simp only [add_sub_cancel_left] at hsval
            dsimp [sp, r] at hsval
            omega
          have hnext : finRotate (m + 1) (a + sp) ∈ w := by
            by_contra hn
            exact hpred_ne (htUnique (a + sp) hpred hn)
          have heqnext : finRotate (m + 1) (a + sp) = a + ss := by
            have hspeq : sp + 1 = ss := by
              apply Fin.ext
              change ((s - 1) + (1 % (m + 1))) % (m + 1) = s
              rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
              rw [Nat.mod_eq_of_lt (by omega : s - 1 + 1 < m + 1)]
              omega
            rw [finRotate_apply]
            rw [← hspeq]
            abel
          rwa [heqnext] at hnext
  have houtside : ∀ s : Nat, (hrs : r.val < s) → (hsm : s ≤ m) →
      a + (⟨s, by omega⟩ : Fin (m + 1)) ∉ w := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro hrs hsm
        by_cases hbase : s = r.val + 1
        · subst s
          have heqnext : a + (⟨r.val + 1, by omega⟩ : Fin (m + 1)) =
              finRotate (m + 1) t := by
            have hrnext : (⟨r.val + 1, by omega⟩ : Fin (m + 1)) = r + 1 := by
              apply Fin.ext
              change r.val + 1 = (r.val + (1 % (m + 1))) % (m + 1)
              rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
              rw [Nat.mod_eq_of_lt (by omega : r.val + 1 < m + 1)]
            rw [hrnext, finRotate_apply, ← htform]
            abel
          rwa [heqnext]
        · have hpredr : r.val < s - 1 := by omega
          have hpredm : s - 1 ≤ m := by omega
          let sp : Fin (m + 1) := ⟨s - 1, by omega⟩
          let ss : Fin (m + 1) := ⟨s, by omega⟩
          have hpred : a + sp ∉ w := ih (s - 1) (by omega) hpredr hpredm
          have hpred_ne : a + sp ≠ a := by
            intro heq
            have heq' := congrArg (fun z : Fin (m + 1) => z - a) heq
            have : sp = 0 := by simpa using heq'
            have : s - 1 = 0 := congrArg Fin.val this
            omega
          have hnext : finRotate (m + 1) (a + sp) ∉ w := by
            intro hn
            have hbound : a + sp ∈ sixVertexBetheMLBoundarySet w :=
              (mem_sixVertexBetheMLBoundarySet w (a + sp)).2 ⟨hpred, hn⟩
            have : a + sp = a := by simpa [hML] using hbound
            exact hpred_ne this
          have heqnext : finRotate (m + 1) (a + sp) = a + ss := by
            have hspeq : sp + 1 = ss := by
              apply Fin.ext
              change ((s - 1) + (1 % (m + 1))) % (m + 1) = s
              rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
              rw [Nat.mod_eq_of_lt (by omega : s - 1 + 1 < m + 1)]
              omega
            rw [finRotate_apply]
            rw [← hspeq]
            abel
          rwa [heqnext] at hnext
  ext k
  rw [mem_sixVertexBetheCyclicWord]
  let q : Fin (m + 1) := k - a
  have hkform : a + q = k := by
    dsimp [q]
    abel
  by_cases hq0 : q.val = 0
  · have hka : k = a := by
      have hqzero : q = 0 := by apply Fin.ext; simpa using hq0
      calc
        k = a + q := hkform.symm
        _ = a := by rw [hqzero]; simp
    constructor
    · intro hkw
      exact (haML.1 (hka ▸ hkw)).elim
    · intro hcond
      have : ¬ 0 < (k - a).val := by rw [hka]; simp
      exact (this hcond.1).elim
  · have hqpos : 0 < q.val := Nat.pos_of_ne_zero hq0
    by_cases hqr : q.val ≤ r.val
    · have hkw := hinside q.val hqpos hqr
      have : a + (⟨q.val, lt_of_le_of_lt hqr r.isLt⟩ : Fin (m + 1)) = k := by
        calc
          _ = a + q := by congr
          _ = k := hkform
      constructor
      · intro _
        exact ⟨by simpa [q] using hqpos, by simpa [q, r] using hqr⟩
      · intro _
        rw [← this]
        exact hkw
    · have hkw := houtside q.val (by omega) (Nat.le_of_lt_succ q.isLt)
      have : a + (⟨q.val, by omega⟩ : Fin (m + 1)) = k := by
        calc
          _ = a + q := by congr
          _ = k := hkform
      constructor
      · intro hk
        exfalso
        apply hkw
        rw [this]
        exact hk
      · intro h
        exact False.elim (hqr (by simpa [r] using h.2))

set_option maxHeartbeats 2000000 in


theorem sixVertexBethePerturbedWordSum_adjacent_tendsto
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 1) → Real) (ell : Fin (n + 1)) (hell : p ell = 0)
    (x : Fin (n + 1) → Int) (w : Finset (Fin (n + 1)))
    (i : Fin n) (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (hML : sixVertexBetheMLBoundarySet w = {i.castSucc})
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    Tendsto (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 *
        ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.succ = ell,
          sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w i.castSucc)) := by
  classical
  let F := nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ
  have hpair (sigma : Equiv.Perm (Fin (n + 1)))
      (hroot : sigma i.succ = ell) :
      Tendsto (fun eps : Real =>
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * Equiv.swap i.castSucc i.succ)) F
        (nhds ((c : Complex) ^ 2 *
          sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w i.castSucc)) := by
    have hab : i.castSucc ≠ i.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hleft : sigma i.castSucc ≠ ell := by
      intro h
      exact hab (sigma.injective (h.trans hroot.symm))
    have hrem (eps : Real) :=
      sixVertexBetheWordCoefficientRemainder_perturb_eq c p ell eps w
        i.castSucc hML sigma (by
          simpa [show finRotate (n + 1) i.castSucc = i.succ by
            apply Fin.ext
            simp] using hroot)
    have hmono :=
      (continuous_sixVertexBethePerturbedWordMonomial
        (N := N) p ell sigma x w).continuousAt.mono_left
          (inf_le_left : F ≤ nhds (0 : Real))
    have hmono0 : sixVertexBetheWordMonomial N
        (fun j => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell 0 j)) sigma x w =
        sixVertexBetheWordMonomial N
          (fun j => sixVertexBethePhase (p j)) sigma x w := by
      unfold sixVertexBetheWordMonomial
      apply Finset.prod_congr rfl
      intro k hk
      have hpert (j : Fin (n + 1)) :
          sixVertexBethePerturbRoot p ell 0 j = p j := by
        by_cases h : j = ell
        · subst j
          simp [sixVertexBethePerturbRoot, hell]
        · simp [sixVertexBethePerturbRoot, h]
      change (if k ∈ w then
          sixVertexBethePhase (sixVertexBethePerturbRoot p ell 0 (sigma k)) ^
            sixVertexBetheShiftCoordinates N x k
        else sixVertexBethePhase (sixVertexBethePerturbRoot p ell 0 (sigma k)) ^ x k) =
        if k ∈ w then sixVertexBethePhase (p (sigma k)) ^
          sixVertexBetheShiftCoordinates N x k
        else sixVertexBethePhase (p (sigma k)) ^ x k
      rw [hpert (sigma k)]
    change Tendsto _ F (nhds (sixVertexBetheWordMonomial N
      (fun j => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell 0 j)) sigma x w)) at hmono
    rw [hmono0] at hmono
    let C : Complex := (c : Complex) ^ 2 *
      sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
      sixVertexBetheM c (sixVertexBethePhase (p (sigma i.castSucc))) *
      sixVertexBetheAmplitude c p sigma *
      sixVertexBetheWordCoefficientRemainder c
        (fun j => sixVertexBethePhase (p j)) sigma w i.castSucc
    have hconst : Tendsto (fun _eps : Real => C) F (nhds C) :=
      tendsto_const_nhds
    have hlim := hconst.mul hmono
    have hlim' : Tendsto (fun eps : Real =>
        ((c : Complex) ^ 2 *
          sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
          sixVertexBetheM c (sixVertexBethePhase (p (sigma i.castSucc))) *
          sixVertexBetheAmplitude c p sigma *
          sixVertexBetheWordCoefficientRemainder c
            (fun j => sixVertexBethePhase (p j)) sigma w i.castSucc) *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase
              (sixVertexBethePerturbRoot p ell eps j)) sigma x w) F
        (nhds ((c : Complex) ^ 2 *
          sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w i.castSucc)) := by
      convert hlim using 1
      congr 1
      dsimp [C]
      unfold sixVertexBetheZeroHatTerm sixVertexBetheZeroHatCoefficient
      ring
    apply hlim'.congr'
    have hne : ∀ᶠ eps in F, eps ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with eps heps
      simpa [F] using heps
    have hinter : ∀ᶠ eps in F, eps ∈ Set.Ioo (-Real.pi) Real.pi :=
      mem_inf_of_left (Ioo_mem_nhds
        (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
    filter_upwards [hne, hinter] with eps hneps heps
    have hphase := sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero
      heps hneps
    rw [sixVertexBethePerturbedWordTerm_adjacent_zero_pair hc p ell hell eps
      hphase x w i hiM hiL sigma hroot hother]
    rw [hrem]
  have hsum : Tendsto (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.succ = ell,
        (sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * Equiv.swap i.castSucc i.succ))) F
      (nhds (∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.succ = ell,
        ((c : Complex) ^ 2 *
          sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w i.castSucc))) := by
    exact tendsto_finset_sum _ fun sigma hsigma =>
      hpair sigma (Finset.mem_filter.mp hsigma).2
  have hsum' : Tendsto (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) F
      (nhds (∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.succ = ell,
        ((c : Complex) ^ 2 *
          sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w i.castSucc))) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall fun eps =>
      (sum_sixVertexBethePerturbedWordTerm_adjacent_eq_zeroPairs
        hc p ell eps x w i hiM hiL hother).symm
  simpa only [Finset.mul_sum, mul_assoc] using hsum'


theorem sixVertexBethePerturbedWordTerm_boundary_zero_pair
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (hlastM : Fin.last (n + 1) ∉ w) (hzeroL : (0 : Fin (n + 2)) ∈ w)
    (sigma : Equiv.Perm (Fin (n + 2))) (hroot : sigma 0 = ell) :
    sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
        sixVertexBethePerturbedWordTerm N c p ell eps x w
          (sigma * Equiv.swap (Fin.last (n + 1)) 0) =
      ((sixVertexBetheM c
            (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) *
          sixVertexBetheL c (sixVertexBethePhase eps) - 1) -
        Complex.exp (-Complex.I * sixVertexTheta c 0
            (p (sigma (Fin.last (n + 1))))) *
          sixVertexBethePhase eps ^ N *
          (sixVertexBetheM c (sixVertexBethePhase eps) *
            sixVertexBetheL c
              (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) - 1)) *
        sixVertexBetheAmplitude c p sigma *
        sixVertexBetheWordCoefficientRemainder c
          (fun j => sixVertexBethePhase
            (sixVertexBethePerturbRoot p ell eps j)) sigma w
              (Fin.last (n + 1)) *
        sixVertexBetheWordMonomial N
          (fun j => sixVertexBethePhase
            (sixVertexBethePerturbRoot p ell eps j)) sigma x w := by
  let a : Fin (n + 2) := Fin.last (n + 1)
  let b : Fin (n + 2) := 0
  let tau := Equiv.swap a b
  let z : Fin (n + 2) → Complex := fun j => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps j)
  let B : Equiv.Perm (Fin (n + 2)) → Complex := fun rho =>
    sixVertexBetheWordCoefficientRemainder c z rho w a *
      sixVertexBetheWordMonomial N z rho x w
  have hrot : finRotate (n + 2) a = b := by
    apply Fin.ext
    simp [a, b]
  have hza : z (sigma a) =
      sixVertexBethePhase (p (sigma a)) := by
    have hne : sigma a ≠ ell := by
      intro h
      have hab : a ≠ b := by simp [a, b]
      exact hab (sigma.injective (h.trans hroot.symm))
    simp [z, sixVertexBethePerturbRoot, hne]
  have hzb : z (sigma b) = sixVertexBethePhase eps := by
    simp [z, b, hroot, sixVertexBethePerturbRoot]
  have hB : sixVertexBethePhase (p (sigma a)) ^ N * B (sigma * tau) =
      sixVertexBethePhase eps ^ N * B sigma := by
    have hrem := sixVertexBetheWordCoefficientRemainder_swap_invariant
      c z sigma w hlastM hzeroL hrot
    have hmon := sixVertexBetheWordMonomial_boundary_covariant (N := N)
      z (fun j => Complex.exp_ne_zero _) sigma x w hlastM hzeroL
    dsimp [B]
    rw [hrem]
    calc
      _ = sixVertexBetheWordCoefficientRemainder c z sigma w a *
          (z (sigma a) ^ N *
            sixVertexBetheWordMonomial N z (sigma * tau) x w) := by
              rw [hza]
              ring
      _ = sixVertexBetheWordCoefficientRemainder c z sigma w a *
          (z (sigma b) ^ N *
            sixVertexBetheWordMonomial N z sigma x w) := by
              simpa [tau, a, b] using congrArg
                (fun q => sixVertexBetheWordCoefficientRemainder c z sigma w a * q)
                hmon
      _ = _ := by rw [hzb]; ring
  have hamp0 := hp.amplitude_boundary_exchange hc sigma
  rw [hroot, hell] at hamp0
  rw [sixVertexBetheBoundaryPermutation_eq_swap n] at hamp0
  have hamp1 : Complex.exp (-Complex.I *
          sixVertexTheta c (p (sigma a)) 0) *
        sixVertexBetheAmplitude c p (sigma * tau) =
      -(sixVertexBethePhase (p (sigma a)) ^ N *
        sixVertexBetheAmplitude c p sigma) := by
    simpa [a, tau, b, sixVertexBethePhase] using hamp0
  have hamp : Complex.exp (Complex.I * sixVertexTheta c 0 (p (sigma a))) *
        sixVertexBetheAmplitude c p (sigma * tau) =
      -(sixVertexBethePhase (p (sigma a)) ^ N *
        sixVertexBetheAmplitude c p sigma) := by
    rw [sixVertexTheta_antisymm c 0 (p (sigma a))] at hamp1
    convert hamp1 using 1
    push_cast
    ring
  have hcancel : Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
      Complex.exp (Complex.I * sixVertexTheta c 0 (p (sigma a))) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hampB : sixVertexBetheAmplitude c p (sigma * tau) * B (sigma * tau) =
      -Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
        sixVertexBethePhase eps ^ N *
          sixVertexBetheAmplitude c p sigma * B sigma := by
    calc
      _ = Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
          (Complex.exp (Complex.I * sixVertexTheta c 0 (p (sigma a))) *
            sixVertexBetheAmplitude c p (sigma * tau)) * B (sigma * tau) := by
              dsimp [B]
              calc
                _ = 1 * (sixVertexBetheAmplitude c p (sigma * tau) *
                    (sixVertexBetheWordCoefficientRemainder c z
                      (sigma * tau) w a *
                      sixVertexBetheWordMonomial N z (sigma * tau) x w)) := by ring
                _ = (Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
                    Complex.exp (Complex.I * sixVertexTheta c 0 (p (sigma a)))) *
                    (sixVertexBetheAmplitude c p (sigma * tau) *
                      (sixVertexBetheWordCoefficientRemainder c z
                        (sigma * tau) w a *
                        sixVertexBetheWordMonomial N z (sigma * tau) x w)) := by
                          rw [hcancel]
                _ = _ := by ring
      _ = -Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
          sixVertexBetheAmplitude c p sigma *
            (sixVertexBethePhase (p (sigma a)) ^ N * B (sigma * tau)) := by
              rw [hamp]
              ring
      _ = _ := by rw [hB]; ring
  unfold sixVertexBethePerturbedWordTerm
  change sixVertexBetheAmplitude c p sigma *
      sixVertexBetheWordCoefficient c z sigma w *
        sixVertexBetheWordMonomial N z sigma x w +
    sixVertexBetheAmplitude c p (sigma * tau) *
      sixVertexBetheWordCoefficient c z (sigma * tau) w *
        sixVertexBetheWordMonomial N z (sigma * tau) x w = _
  rw [sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder
      c z sigma w hlastM hzeroL hrot,
    sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder
      c z (sigma * tau) w hlastM hzeroL hrot]
  dsimp only [tau, a, b]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  have hampB' : sixVertexBetheAmplitude c p
        (sigma * Equiv.swap (Fin.last (n + 1)) 0) *
      (sixVertexBetheWordCoefficientRemainder c z
          (sigma * Equiv.swap (Fin.last (n + 1)) 0) w (Fin.last (n + 1)) *
        sixVertexBetheWordMonomial N z
          (sigma * Equiv.swap (Fin.last (n + 1)) 0) x w) =
      -Complex.exp (-Complex.I * sixVertexTheta c 0
          (p (sigma (Fin.last (n + 1))))) *
        sixVertexBethePhase eps ^ N *
          sixVertexBetheAmplitude c p sigma *
            (sixVertexBetheWordCoefficientRemainder c z sigma w
                (Fin.last (n + 1)) *
              sixVertexBetheWordMonomial N z sigma x w) := by
    simpa [B, tau, a, b] using hampB
  rw [hza, hzb]
  dsimp only [a]
  rw [show sixVertexBetheAmplitude c p
        (sigma * Equiv.swap (Fin.last (n + 1)) 0) *
      ((sixVertexBetheM c (sixVertexBethePhase eps) *
          sixVertexBetheL c (sixVertexBethePhase
            (p (sigma (Fin.last (n + 1))))) - 1) *
        sixVertexBetheWordCoefficientRemainder c z
          (sigma * Equiv.swap (Fin.last (n + 1)) 0) w (Fin.last (n + 1))) *
        sixVertexBetheWordMonomial N z
          (sigma * Equiv.swap (Fin.last (n + 1)) 0) x w =
      (sixVertexBetheM c (sixVertexBethePhase eps) *
          sixVertexBetheL c (sixVertexBethePhase
            (p (sigma (Fin.last (n + 1))))) - 1) *
        (sixVertexBetheAmplitude c p
          (sigma * Equiv.swap (Fin.last (n + 1)) 0) *
          (sixVertexBetheWordCoefficientRemainder c z
            (sigma * Equiv.swap (Fin.last (n + 1)) 0) w (Fin.last (n + 1)) *
           sixVertexBetheWordMonomial N z
            (sigma * Equiv.swap (Fin.last (n + 1)) 0) x w)) by ring,
    hampB']
  dsimp [a, B, z]
  ring

set_option maxHeartbeats 2000000 in

theorem sixVertexBethePerturbedWordSum_boundary_tendsto
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (x : Fin (n + 2) → Int) (w : Finset (Fin (n + 2)))
    (hlastM : Fin.last (n + 1) ∉ w) (hzeroL : (0 : Fin (n + 2)) ∈ w)
    (hML : sixVertexBetheMLBoundarySet w = {Fin.last (n + 1)})
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    Tendsto (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin (n + 2)),
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 *
        ∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma 0 = ell,
          (sixVertexThetaLeftDerivAtZero c
              (p (sigma (Fin.last (n + 1)))) + N) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w
              (Fin.last (n + 1)))) := by
  classical
  let F := nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ
  have hpair (sigma : Equiv.Perm (Fin (n + 2))) (hroot : sigma 0 = ell) :
      Tendsto (fun eps : Real =>
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * Equiv.swap (Fin.last (n + 1)) 0)) F
        (nhds ((c : Complex) ^ 2 *
          (sixVertexThetaLeftDerivAtZero c
              (p (sigma (Fin.last (n + 1)))) + N) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w
              (Fin.last (n + 1)))) := by
    let a : Fin (n + 2) := Fin.last (n + 1)
    have hleft : sigma a ≠ ell := by
      intro h
      have ha0 : a ≠ 0 := by simp [a]
      exact ha0 (sigma.injective (h.trans hroot.symm))
    have hphase := hother _ hleft
    have hfactor := sixVertexBetheZeroBoundaryPairFactor_tendsto
      (N := N) hc hphase
    have hrem (eps : Real) :=
      sixVertexBetheWordCoefficientRemainder_perturb_eq c p ell eps w a
        hML sigma (by simpa [a] using hroot)
    have hmono :=
      (continuous_sixVertexBethePerturbedWordMonomial
        (N := N) p ell sigma x w).continuousAt.mono_left
          (inf_le_left : F ≤ nhds (0 : Real))
    have hpert (j : Fin (n + 2)) :
        sixVertexBethePerturbRoot p ell 0 j = p j := by
      by_cases h : j = ell
      · subst j
        simp [sixVertexBethePerturbRoot, hell]
      · simp [sixVertexBethePerturbRoot, h]
    have hmono0 : sixVertexBetheWordMonomial N
        (fun j => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell 0 j)) sigma x w =
        sixVertexBetheWordMonomial N
          (fun j => sixVertexBethePhase (p j)) sigma x w := by
      unfold sixVertexBetheWordMonomial
      apply Finset.prod_congr rfl
      intro k hk
      change (if k ∈ w then
          sixVertexBethePhase (sixVertexBethePerturbRoot p ell 0 (sigma k)) ^
            sixVertexBetheShiftCoordinates N x k
        else sixVertexBethePhase (sixVertexBethePerturbRoot p ell 0 (sigma k)) ^ x k) =
        if k ∈ w then sixVertexBethePhase (p (sigma k)) ^
          sixVertexBetheShiftCoordinates N x k
        else sixVertexBethePhase (p (sigma k)) ^ x k
      rw [hpert]
    change Tendsto _ F (nhds (sixVertexBetheWordMonomial N
      (fun j => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell 0 j)) sigma x w)) at hmono
    rw [hmono0] at hmono
    let R : Complex := sixVertexBetheAmplitude c p sigma *
      sixVertexBetheWordCoefficientRemainder c
        (fun j => sixVertexBethePhase (p j)) sigma w a
    have hR : Tendsto (fun _eps : Real => R) F (nhds R) := tendsto_const_nhds
    have hlim := (hfactor.mul hR).mul hmono
    have hlim' : Tendsto (fun eps : Real =>
        (((sixVertexBetheM c (sixVertexBethePhase (p (sigma a))) *
              sixVertexBetheL c (sixVertexBethePhase eps) - 1) -
            Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
              sixVertexBethePhase eps ^ N *
              (sixVertexBetheM c (sixVertexBethePhase eps) *
                sixVertexBetheL c (sixVertexBethePhase (p (sigma a))) - 1)) *
          R) *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase
              (sixVertexBethePerturbRoot p ell eps j)) sigma x w) F
        (nhds ((c : Complex) ^ 2 *
          (sixVertexThetaLeftDerivAtZero c (p (sigma a)) + N) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w a)) := by
      convert hlim using 1
      congr 1
      dsimp [R]
      unfold sixVertexBetheZeroHatTerm sixVertexBetheZeroHatCoefficient
      ring
    apply hlim'.congr'
    filter_upwards with eps
    rw [sixVertexBethePerturbedWordTerm_boundary_zero_pair
      hc p hp ell hell eps x w hlastM hzeroL sigma hroot]
    rw [hrem]
    dsimp [R, a]
    ring
  have hsum : Tendsto (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma 0 = ell,
        (sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * Equiv.swap (Fin.last (n + 1)) 0))) F
      (nhds (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma 0 = ell,
        ((c : Complex) ^ 2 *
          (sixVertexThetaLeftDerivAtZero c
              (p (sigma (Fin.last (n + 1)))) + N) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w
              (Fin.last (n + 1))))) := by
    exact tendsto_finset_sum _ fun sigma hsigma =>
      hpair sigma (Finset.mem_filter.mp hsigma).2
  have hsum' : Tendsto (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin (n + 2)),
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) F
      (nhds (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma 0 = ell,
        ((c : Complex) ^ 2 *
          (sixVertexThetaLeftDerivAtZero c
              (p (sigma (Fin.last (n + 1)))) + N) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x w
              (Fin.last (n + 1))))) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall fun eps =>
      (sum_sixVertexBethePerturbedWordTerm_boundary_eq_zeroPairs
        hc p hp ell eps x w hlastM hzeroL hother).symm
  simpa only [Finset.mul_sum, mul_assoc] using hsum'


theorem sum_singleMLWords_eq_cyclicWords
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (x : Fin (n + 2) → Int)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (f : Finset (Fin (n + 2)) → Complex) :
    (∑ w : Finset (Fin (n + 2)) with
        (sixVertexBetheMLBoundarySet w).card = 1, f w) =
      ∑ a : Fin (n + 2),
        ∑ t : Fin (n + 2) with t ≠ a, f (sixVertexBetheCyclicWord a t) := by
  classical
  have hsplit : (∑ w : Finset (Fin (n + 2)) with
      (sixVertexBetheMLBoundarySet w).card = 1, f w) =
      ∑ a : Fin (n + 2),
        ∑ w : Finset (Fin (n + 2)) with
          sixVertexBetheMLBoundarySet w = {a}, f w := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hcard : (sixVertexBetheMLBoundarySet w).card = 1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      rw [ha]
      simp
    · simp only [if_neg hcard]
      symm
      apply Finset.sum_eq_zero
      intro a ha
      rw [if_neg]
      intro heq
      apply hcard
      rw [heq]
      simp
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro a ha
  symm
  apply Finset.sum_bij (fun t _ => sixVertexBetheCyclicWord a t)
  · intro t ht
    have hta : t ≠ a := (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      sixVertexBetheCyclicWord_MLBoundarySet a t hta.symm⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    have h₁ := sixVertexBetheCyclicWord_unique_LM a t₁
      (Finset.mem_filter.mp ht₁).2.symm
    have h₂ := sixVertexBetheCyclicWord_unique_LM a t₂
      (Finset.mem_filter.mp ht₂).2.symm
    exact (h₁.2.2 t₂ (heq ▸ h₂.1) (heq ▸ h₂.2.1)).symm
  · intro w hw
    have hML := (Finset.mem_filter.mp hw).2
    obtain ⟨t, tau, htw, htend, htUnique, htau, hout, hterm⟩ :=
      sixVertexBetheZeroHatTerm_normalize_mulRight hc p hp ell hell x w a hML hother
    have haM := ((mem_sixVertexBetheMLBoundarySet w a).mp (by simp [hML])).1
    have hta : t ≠ a := fun h => haM (h.symm ▸ htw)
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hta⟩, ?_⟩
    exact (eq_sixVertexBetheCyclicWord_of_boundaries
      w a t hML htw htend htUnique).symm
  · intro t ht
    rfl

theorem sum_marked_zero_slot
    {m : Nat} (ell : Fin (m + 1))
    (F : Fin (m + 1) → Complex)
    (W : Equiv.Perm (Fin (m + 1)) → Complex) :
    (∑ a : Fin (m + 1), ∑ t : Fin (m + 1) with t ≠ a,
      ∑ rho : Equiv.Perm (Fin (m + 1)) with rho t = ell,
        F (rho a) * W rho) =
      (∑ j : Fin (m + 1) with j ≠ ell, F j) * ∑ rho, W rho := by
  classical
  calc
    _ = ∑ a : Fin (m + 1), ∑ t : Fin (m + 1),
        ∑ rho : Equiv.Perm (Fin (m + 1)),
          if t ≠ a ∧ rho t = ell then F (rho a) * W rho else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_filter]
      by_cases hta : t = a
      · simp [hta]
      · simp [hta]
    _ = ∑ a : Fin (m + 1), ∑ rho : Equiv.Perm (Fin (m + 1)),
        ∑ t : Fin (m + 1),
          if t ≠ a ∧ rho t = ell then F (rho a) * W rho else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ rho : Equiv.Perm (Fin (m + 1)), ∑ a : Fin (m + 1),
        ∑ t : Fin (m + 1),
          if t ≠ a ∧ rho t = ell then F (rho a) * W rho else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ rho : Equiv.Perm (Fin (m + 1)), ∑ t : Fin (m + 1),
        ∑ a : Fin (m + 1),
          if t ≠ a ∧ rho t = ell then F (rho a) * W rho else 0 := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [Finset.sum_comm]
    _ = ∑ rho : Equiv.Perm (Fin (m + 1)),
        (∑ a : Fin (m + 1) with a ≠ rho.symm ell, F (rho a)) * W rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [Finset.sum_eq_single (rho.symm ell)]
      · rw [Finset.sum_filter, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : a = rho.symm ell <;> simp [h, ne_comm]
      · intro t ht hne
        apply Finset.sum_eq_zero
        intro a ha
        rw [if_neg (fun h =>
          hne (rho.injective (h.2.trans (rho.apply_symm_apply ell).symm)))]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = ∑ rho : Equiv.Perm (Fin (m + 1)),
        (∑ j : Fin (m + 1) with j ≠ ell, F j) * W rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      congr 1
      rw [Finset.sum_filter, Finset.sum_filter]
      have hreindex := Equiv.sum_comp rho
        (fun j : Fin (m + 1) => if j ≠ ell then F j else 0)
      calc
        (∑ a, if a ≠ rho.symm ell then F (rho a) else 0) =
            ∑ a, if rho a ≠ ell then F (rho a) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases h : ell = rho a
          · have hra : rho a = ell := h.symm
            have h' : a = rho.symm ell := by
              apply rho.injective
              simpa using hra
            rw [if_neg (not_ne_iff.mpr h'), if_neg (not_ne_iff.mpr hra)]
          · have h' : a ≠ rho.symm ell := by
              intro ha'
              apply h
              rw [ha']
              simp
            have hra : rho a ≠ ell := Ne.symm h
            rw [if_pos h', if_pos hra]
        _ = _ := hreindex
    _ = _ := by rw [Finset.mul_sum]

theorem sum_zero_slot_except_last
    {m : Nat} (ell : Fin (m + 1))
    (W : Equiv.Perm (Fin (m + 1)) → Complex) :
    (∑ t : Fin (m + 1) with t ≠ Fin.last m,
      ∑ rho : Equiv.Perm (Fin (m + 1)) with rho t = ell, W rho) =
      (∑ rho, W rho) -
        ∑ rho : Equiv.Perm (Fin (m + 1)) with rho (Fin.last m) = ell,
          W rho := by
  classical
  have hleft : (∑ t : Fin (m + 1), ∑ rho : Equiv.Perm (Fin (m + 1)),
      if t ≠ Fin.last m ∧ rho t = ell then W rho else 0) =
      ∑ rho : Equiv.Perm (Fin (m + 1)),
        if rho (Fin.last m) ≠ ell then W rho else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [Finset.sum_eq_single (rho.symm ell)]
    · by_cases h : rho.symm ell = Fin.last m
      · have h' : rho (Fin.last m) = ell := by
          rw [← h]
          simp
        simp [h, h']
      · have h' : rho (Fin.last m) ≠ ell := by
          intro hr
          apply h
          exact rho.injective (by simpa using hr.symm)
        simp [h, h']
    · intro t ht hne
      rw [if_neg]
      intro h
      exact hne (rho.injective (h.2.trans (rho.apply_symm_apply ell).symm))
    · intro h
      exact (h (Finset.mem_univ _)).elim
  calc
    _ = ∑ t : Fin (m + 1), ∑ rho : Equiv.Perm (Fin (m + 1)),
        if t ≠ Fin.last m ∧ rho t = ell then W rho else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_filter]
      by_cases hlast : t = Fin.last m <;> simp [hlast]
    _ = ∑ rho : Equiv.Perm (Fin (m + 1)),
        if rho (Fin.last m) ≠ ell then W rho else 0 := hleft
    _ = _ := by
      rw [Finset.sum_filter]
      calc
        (∑ rho, if rho (Fin.last m) ≠ ell then W rho else 0) =
        ∑ rho, (W rho - if rho (Fin.last m) = ell then W rho else 0) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          by_cases h : rho (Fin.last m) = ell <;> simp [h]
        _ = _ := by rw [Finset.sum_sub_distrib]

set_option maxHeartbeats 2000000 in
theorem sum_singleML_zeroHatTerms
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (x : Fin (n + 2) → Int)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
      (c : Complex) ^ 2 *
        ∑ sigma : Equiv.Perm (Fin (n + 2)) with
            sigma (finRotate (n + 2) a) = ell,
          (sixVertexThetaLeftDerivAtZero c (p (sigma a)) +
              if a = Fin.last (n + 1) then N else 0) *
            sixVertexBetheZeroHatTerm (N := N) c p sigma x
              (sixVertexBetheCyclicWord a t) a) =
      (c : Complex) ^ 2 *
        (((N : Complex) + ∑ j ∈ Finset.univ.erase ell,
            (sixVertexThetaLeftDerivAtZero c (p j) : Complex)) *
          (∏ j ∈ Finset.univ.erase ell,
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          sixVertexCoordinateBetheIntWave c p x -
        (N : Complex) * (∏ j ∈ Finset.univ.erase ell,
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          ∑ rho : Equiv.Perm (Fin (n + 2)) with
              rho (Fin.last (n + 1)) = ell,
            sixVertexBetheAmplitude c p rho *
              sixVertexBetheIntMonomial p rho x) := by
  classical
  let D : Fin (n + 2) → Complex := fun j =>
    sixVertexThetaLeftDerivAtZero c (p j)
  let W : Equiv.Perm (Fin (n + 2)) → Complex := fun rho =>
    sixVertexBetheAmplitude c p rho * sixVertexBetheIntMonomial p rho x
  let MP : Complex := ∏ j ∈ Finset.univ.erase ell,
    sixVertexBetheM c (sixVertexBethePhase (p j))
  have hpoint (a t : Fin (n + 2)) (hta : t ≠ a) :
      (∑ sigma : Equiv.Perm (Fin (n + 2)) with
          sigma (finRotate (n + 2) a) = ell,
        (D (sigma a) + if a = Fin.last (n + 1) then N else 0) *
          sixVertexBetheZeroHatTerm (N := N) c p sigma x
            (sixVertexBetheCyclicWord a t) a) =
        MP * ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell,
          (D (rho a) + if a = Fin.last (n + 1) then N else 0) * W rho := by
    have hML := sixVertexBetheCyclicWord_MLBoundarySet a t hta.symm
    obtain ⟨u, hu, huend, hsum⟩ := sum_sixVertexBetheZeroHatTerm_eq_terminal
      hc p hp ell hell x (sixVertexBetheCyclicWord a t) a hML hother
        (fun j => D j + if a = Fin.last (n + 1) then N else 0)
    have hend := sixVertexBetheCyclicWord_unique_LM a t hta.symm
    have hut : u = t := hend.2.2 u hu huend
    subst u
    simpa [D, W, MP, mul_assoc] using hsum
  have hN : (∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
      ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell,
        (if a = Fin.last (n + 1) then (N : Complex) else 0) * W rho) =
      N * (∑ t : Fin (n + 2) with t ≠ Fin.last (n + 1),
        ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell, W rho) := by
    rw [Finset.sum_eq_single (Fin.last (n + 1))]
    · simp_rw [Finset.mul_sum]
      simp
    · intro a ha hne
      simp [hne]
    · simp
  have hfactor (G : Fin (n + 2) → Fin (n + 2) → Complex) :
      (∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a, MP * G a t) =
        MP * ∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a, G a t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
  calc
    _ = (c : Complex) ^ 2 *
        ∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
          MP * ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell,
            (D (rho a) + if a = Fin.last (n + 1) then N else 0) * W rho := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [hpoint a t (Finset.mem_filter.mp ht).2]
    _ = (c : Complex) ^ 2 * MP *
        ((∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
            ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell,
              D (rho a) * W rho) +
          N * (∑ t : Fin (n + 2) with t ≠ Fin.last (n + 1),
            ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell, W rho)) := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [hfactor]
      simp_rw [Finset.sum_add_distrib]
      simp_rw [Nat.cast_ite, Nat.cast_zero]
      rw [hN]
      ring
    _ = (c : Complex) ^ 2 * MP *
        (((∑ j : Fin (n + 2) with j ≠ ell, D j) * ∑ rho, W rho) +
          N * ((∑ rho, W rho) -
            ∑ rho : Equiv.Perm (Fin (n + 2)) with
                rho (Fin.last (n + 1)) = ell, W rho)) := by
      rw [sum_marked_zero_slot ell D W,
        sum_zero_slot_except_last ell W]
    _ = _ := by
      dsimp [D, W, MP]
      rw [show Finset.univ.filter (fun j : Fin (n + 2) => j ≠ ell) =
        Finset.univ.erase ell by
          ext j
          simp]
      change _ = (c : Complex) ^ 2 * _
      unfold sixVertexCoordinateBetheIntWave
      ring

set_option maxHeartbeats 2000000 in


theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedSingleMLWordTotal_tendsto
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : Fin (n + 2) → Int) :
    Tendsto (sixVertexBethePerturbedSingleMLWordTotal N c p ell x)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 *
        (((N : Complex) + ∑ j ∈ Finset.univ.erase ell,
            (sixVertexThetaLeftDerivAtZero c (p j) : Complex)) *
          (∏ j ∈ Finset.univ.erase ell,
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          sixVertexCoordinateBetheIntWave c p x -
        (N : Complex) * (∏ j ∈ Finset.univ.erase ell,
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          ∑ rho : Equiv.Perm (Fin (n + 2)) with
              rho (Fin.last (n + 1)) = ell,
            sixVertexBetheAmplitude c p rho *
              sixVertexBetheIntMonomial p rho x))) := by
  classical
  let F := nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ
  let L : Fin (n + 2) → Fin (n + 2) → Complex := fun a t =>
    (c : Complex) ^ 2 *
      ∑ sigma : Equiv.Perm (Fin (n + 2)) with
          sigma (finRotate (n + 2) a) = ell,
        (sixVertexThetaLeftDerivAtZero c (p (sigma a)) +
            if a = Fin.last (n + 1) then N else 0) *
          sixVertexBetheZeroHatTerm (N := N) c p sigma x
            (sixVertexBetheCyclicWord a t) a
  have hlocal (a t : Fin (n + 2)) (hta : t ≠ a) :
      Tendsto (fun eps : Real =>
        ∑ sigma : Equiv.Perm (Fin (n + 2)),
          sixVertexBethePerturbedWordTerm N c p ell eps x
            (sixVertexBetheCyclicWord a t) sigma) F (nhds (L a t)) := by
    let w := sixVertexBetheCyclicWord a t
    have hML := sixVertexBetheCyclicWord_MLBoundarySet a t hta.symm
    have haML := (mem_sixVertexBetheMLBoundarySet w a).mp (by simp [w, hML])
    by_cases haLast : a = Fin.last (n + 1)
    · subst a
      have hzeroL : (0 : Fin (n + 2)) ∈ w := by
        have := haML.2
        simpa [w] using this
      simpa [L, w] using
        sixVertexBethePerturbedWordSum_boundary_tendsto hc p hp ell hell x w
          haML.1 hzeroL hML hother
    · have haval : a.val < n + 1 := by
        have hle : a.val ≤ n + 1 := by omega
        have hne : a.val ≠ n + 1 := by
          intro h
          apply haLast
          apply Fin.ext
          simpa using h
        omega
      let i : Fin (n + 1) := ⟨a.val, haval⟩
      have hia : i.castSucc = a := by apply Fin.ext; rfl
      have hirot : i.succ = finRotate (n + 2) a := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last haLast]
        rfl
      have hiM : i.castSucc ∉ w := by simpa [hia] using haML.1
      have hiL : i.succ ∈ w := by simpa [hirot] using haML.2
      simpa [L, w, haLast, hia, hirot] using
        sixVertexBethePerturbedWordSum_adjacent_tendsto hc p ell hell x w i
          hiM hiL (by simpa [hia] using hML) hother
  have hsum : Tendsto (fun eps : Real =>
      ∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
        ∑ sigma : Equiv.Perm (Fin (n + 2)),
          sixVertexBethePerturbedWordTerm N c p ell eps x
            (sixVertexBetheCyclicWord a t) sigma) F
      (nhds (∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
        L a t)) := by
    exact tendsto_finset_sum _ fun a ha =>
      tendsto_finset_sum _ fun t ht =>
        hlocal a t (Finset.mem_filter.mp ht).2
  have hsum' : Tendsto (sixVertexBethePerturbedSingleMLWordTotal N c p ell x)
      F (nhds (∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
        L a t)) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall fun eps => by
      unfold sixVertexBethePerturbedSingleMLWordTotal
      exact (sum_singleMLWords_eq_cyclicWords hc p hp ell hell x hother
        (fun w => ∑ sigma : Equiv.Perm (Fin (n + 2)),
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma)).symm
  have hvalue := sum_singleML_zeroHatTerms hc p hp ell hell x hother
  change (∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a,
      L a t) = _ at hvalue
  rwa [hvalue] at hsum'

theorem sixVertexBetheMLBoundarySet_card_eq_zero_iff
    {n : Nat} (w : Finset (Fin (n + 1))) :
    (sixVertexBetheMLBoundarySet w).card = 0 ↔
      w = ∅ ∨ w = Finset.univ := by
  constructor
  · intro hcard
    by_cases he : w = ∅
    · exact Or.inl he
    · by_cases hu : w = Finset.univ
      · exact Or.inr hu
      · have hnon := sixVertexBetheMLBoundarySet_nonempty_of_nonempty_ne_univ
          w he hu
        exact False.elim (by
          rw [Finset.card_eq_zero.mp hcard] at hnon
          simpa using hnon)
  · rintro (rfl | rfl) <;>
      simp [sixVertexBetheMLBoundarySet]

theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_eq_constant_add_single
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2))
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : Fin (n + 2) → Int) (eps : Real) :
    sixVertexBethePerturbedWordTotal N c p ell x eps =
      sixVertexBethePerturbedConstantWordTotal N c p ell x eps +
        sixVertexBethePerturbedSingleMLWordTotal N c p ell x eps := by
  classical
  let S : Finset (Fin (n + 2)) → Complex := fun w =>
    ∑ sigma : Equiv.Perm (Fin (n + 2)),
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
  have hpart : (∑ w : Finset (Fin (n + 2)), S w) =
      (∑ w : Finset (Fin (n + 2)) with
          (sixVertexBetheMLBoundarySet w).card = 0, S w) +
      (∑ w : Finset (Fin (n + 2)) with
          (sixVertexBetheMLBoundarySet w).card = 1, S w) +
      (∑ w : Finset (Fin (n + 2)) with
          1 < (sixVertexBetheMLBoundarySet w).card, S w) := by
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h0 : (sixVertexBetheMLBoundarySet w).card = 0
    · simp [h0]
    · by_cases h1 : (sixVertexBetheMLBoundarySet w).card = 1
      · simp [h0, h1]
      · have hm : 1 < (sixVertexBetheMLBoundarySet w).card := by omega
        simp [h0, h1, hm]
  have hconst : (∑ w : Finset (Fin (n + 2)) with
      (sixVertexBetheMLBoundarySet w).card = 0, S w) =
      sixVertexBethePerturbedConstantWordTotal N c p ell x eps := by
    have hset : Finset.univ.filter (fun w : Finset (Fin (n + 2)) =>
        (sixVertexBetheMLBoundarySet w).card = 0) = {∅, Finset.univ} := by
      ext w
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact sixVertexBetheMLBoundarySet_card_eq_zero_iff w
    change (∑ w ∈ Finset.univ.filter (fun w : Finset (Fin (n + 2)) =>
        (sixVertexBetheMLBoundarySet w).card = 0), S w) = _
    rw [hset]
    have heu : (∅ : Finset (Fin (n + 2))) ≠ Finset.univ := by
      intro h
      have : (0 : Fin (n + 2)) ∈ (∅ : Finset (Fin (n + 2))) := by
        rw [h]
        simp
      simp at this
    simp [heu, S, sixVertexBethePerturbedConstantWordTotal,
      Finset.sum_add_distrib]
  have hmulti : (∑ w : Finset (Fin (n + 2)) with
      1 < (sixVertexBetheMLBoundarySet w).card, S w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    exact sum_sixVertexBethePerturbedWordTerm_eq_zero_of_multiple_ML
      hc p hp ell eps x w (Finset.mem_filter.mp hw).2 hother
  unfold sixVertexBethePerturbedWordTotal
  simp_rw [Finset.mul_sum]
  have hterm (sigma : Equiv.Perm (Fin (n + 2)))
      (w : Finset (Fin (n + 2))) :
      sixVertexBetheAmplitude c p sigma *
          (sixVertexBetheWordCoefficient c
              (fun j => sixVertexBethePhase
                (sixVertexBethePerturbRoot p ell eps j)) sigma w *
            sixVertexBetheWordMonomial N
              (fun j => sixVertexBethePhase
                (sixVertexBethePerturbRoot p ell eps j)) sigma x w) =
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
    unfold sixVertexBethePerturbedWordTerm
    ring
  simp_rw [hterm]
  change (∑ sigma : Equiv.Perm (Fin (n + 2)),
      ∑ w : Finset (Fin (n + 2)),
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = _
  rw [Finset.sum_comm]
  change (∑ w : Finset (Fin (n + 2)), S w) = _
  rw [hpart, hconst, hmulti, add_zero]
  rfl

set_option maxHeartbeats 1000000 in
theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_tendsto_zeroPhaseEigenvalue
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : Fin (n + 2) → Int) :
    Tendsto (sixVertexBethePerturbedWordTotal N c p ell x)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell *
        sixVertexCoordinateBetheIntWave c p x)) := by
  have h₀ := hp.perturbedConstantWordTotal_tendsto hc p ell hell hother x
  have h₁ := hp.perturbedSingleMLWordTotal_tendsto hc p ell hell hother x
  have hsum := h₀.add h₁
  have hsum' : Tendsto (sixVertexBethePerturbedWordTotal N c p ell x)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (
        (((2 : Complex) - (c : Complex) ^ 2) *
          (∏ j ∈ Finset.univ.erase ell,
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          sixVertexCoordinateBetheIntWave c p x +
        (c : Complex) ^ 2 * N *
          (∏ j ∈ Finset.univ.erase ell,
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          ∑ sigma with sigma (Fin.last (n + 1)) = ell,
            sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial p sigma x) +
        (c : Complex) ^ 2 *
          (((N : Complex) + ∑ j ∈ Finset.univ.erase ell,
              (sixVertexThetaLeftDerivAtZero c (p j) : Complex)) *
            (∏ j ∈ Finset.univ.erase ell,
              sixVertexBetheM c (sixVertexBethePhase (p j))) *
            sixVertexCoordinateBetheIntWave c p x -
          (N : Complex) * (∏ j ∈ Finset.univ.erase ell,
              sixVertexBetheM c (sixVertexBethePhase (p j))) *
            ∑ rho with rho (Fin.last (n + 1)) = ell,
              sixVertexBetheAmplitude c p rho *
                sixVertexBetheIntMonomial p rho x))) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall fun eps =>
      (hp.perturbedWordTotal_eq_constant_add_single hc p ell hother x eps).symm
  convert hsum' using 1
  congr 1
  unfold sixVertexZeroPhaseBetheEigenvalueCandidate
    sixVertexZeroPhaseBethePrefactor
  push_cast
  ring


theorem sixVertexCoordinateBetheZeroPhaseEigenrelation
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (hell : p ell = 0)
    (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p ell := by
  unfold SixVertexCoordinateBetheZeroPhaseEigenrelation
  funext x
  have hphysical := hp.perturbedWordTotal_tendsto_physicalAction
    hc p ell hell hopen hother x
  have heigen := hp.perturbedWordTotal_tendsto_zeroPhaseEigenvalue
    hc p ell hell hother (sixVertexSectorIntCoordinates x)
  letI : NeBot (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) :=
    mem_closure_iff_nhdsWithin_neBot.mp <| by
      rw [Metric.mem_closure_iff]
      intro eps heps
      refine ⟨eps / 2, ?_, ?_⟩
      · simp only [Set.mem_compl_iff]
        intro heq
        have heq' : eps / 2 = 0 := Set.mem_singleton_iff.mp heq
        linarith
      · rw [Real.dist_eq]
        rw [abs_of_nonpos (by linarith)]
        linarith
  have heq := tendsto_nhds_unique hphysical heigen
  simpa only [Pi.smul_apply, smul_eq_mul,
    sixVertexCoordinateBetheWave_eq_intWave] using heq


theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseEigenrelation_of_two_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hn : 2 ≤ n)
    (p : Fin n → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p)
    (ell : Fin n) (hell : p ell = 0)
    (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p ell := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact sixVertexCoordinateBetheZeroPhaseEigenrelation
    hc p hp ell hell hopen hother


theorem sixVertexZeroPhaseMProduct_eq_normProduct_of_symmetric
    {c : Real} (hc : 2 < c) {n : Nat} (p : Fin n → Real) (ell : Fin n)
    (hsymm : ∀ j, p j.rev = -p j) (hellrev : ell.rev = ell)
    (hunique : ∀ j, p j = 0 → j = ell) :
    (∏ j ∈ Finset.univ.erase ell,
        sixVertexBetheM c (sixVertexBethePhase (p j))) =
      ((∏ j ∈ Finset.univ.erase ell,
        ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ : Real) : Complex) := by
  let f : Fin n → Complex := fun j =>
    sixVertexBetheM c (sixVertexBethePhase (p j)) /
      (‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ : Complex)
  have hnorm_ne (j : Fin n) :
      ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sixVertexBetheM_phase_ne_zero hc (p j))
  have hrev_mem (j : Fin n) (hj : j ∈ Finset.univ.erase ell) :
      j.rev ∈ Finset.univ.erase ell := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
    intro hrev
    apply hj
    rw [← hellrev, ← hrev, Fin.rev_rev]
  have hpair (j : Fin n) (hj : j ∈ Finset.univ.erase ell) :
      f j * f j.rev = 1 := by
    have hMrev : sixVertexBetheM c (sixVertexBethePhase (p j.rev)) =
        star (sixVertexBetheM c (sixVertexBethePhase (p j))) := by
      rw [hsymm, sixVertexBetheM_phase_neg]
    simp only [f, hMrev, norm_star]
    rw [div_mul_div_comm, show
      sixVertexBetheM c (sixVertexBethePhase (p j)) *
          star (sixVertexBetheM c (sixVertexBethePhase (p j))) =
        (‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ : Complex) ^ 2 by
          simpa using Complex.mul_conj'
            (sixVertexBetheM c (sixVertexBethePhase (p j)))]
    field_simp [hnorm_ne j]
  have hrev_ne (j : Fin n) (hj : j ∈ Finset.univ.erase ell) :
      j.rev ≠ j := by
    intro hfix
    have hjzero : p j = 0 := by
      have h := hsymm j
      rw [hfix] at h
      linarith
    have hjell := hunique j hjzero
    exact (Finset.ne_of_mem_erase hj) hjell
  have hphaseProd : ∏ j ∈ Finset.univ.erase ell, f j = 1 := by
    exact Finset.prod_involution (s := Finset.univ.erase ell)
      (f := f) (fun j _ => j.rev) hpair
      (fun j hj _ => hrev_ne j hj) hrev_mem
      (fun j hj => Fin.rev_rev j)
  dsimp only [f] at hphaseProd
  rw [Finset.prod_div_distrib] at hphaseProd
  have hnormProd_ne :
      (∏ j ∈ Finset.univ.erase ell,
        (‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ : Complex)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact_mod_cast hnorm_ne j
  rw [Complex.ofReal_prod]
  exact (div_eq_one_iff_eq hnormProd_ne).mp hphaseProd


theorem sixVertexFixedChargeBetheRoots_physicalZeroPhaseEigenrelation_of_odd_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    SixVertexCoordinateBetheZeroPhaseEigenrelation
      (N := sixVertexFourWidth r k) c
      (sixVertexFixedChargeBetheRoots hc r k)
      (sixVertexFixedChargeBetheCentralIndex r k) := by
  have hn : 2 ≤ sixVertexFixedChargeBetheParticleCount r k := by
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    rcases hr with ⟨s, rfl⟩
    omega
  exact SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseEigenrelation_of_two_le
    hc hn (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheRoots_is_multiplicativeSolution hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)
    (sixVertexFixedChargeBetheRoots_mem_open hc r k).2.2
    (fun j hj =>
      sixVertexFixedChargeBetheRoots_phase_ne_one_of_odd_charge_of_ne
        hc hr k hj)


theorem sixVertexFixedOddChargeBetheEigenvalueCandidate_eq_value
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexFixedOddChargeBetheEigenvalueCandidate hc r k =
      (sixVertexFixedOddChargeBetheEigenvalueValue hc r k : Complex) := by
  let p := sixVertexFixedChargeBetheRoots hc r k
  let ell := sixVertexFixedChargeBetheCentralIndex r k
  have hell : p ell = 0 :=
    sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k
  have hellrev : ell.rev = ell := by
    apply (sixVertexFixedChargeBetheRoots_mem_open hc r k).1.injective
    change p ell.rev = p ell
    have hsymm := (sixVertexFixedChargeBetheRoots_mem_open hc r k).2.1 ell
    change p ell.rev = -p ell at hsymm
    rw [hsymm, hell, neg_zero]
  have hunique : ∀ j, p j = 0 → j = ell := by
    intro j hj
    exact (sixVertexFixedChargeBetheRoots_mem_open hc r k).1.injective
      (hj.trans hell.symm)
  have hprod := sixVertexZeroPhaseMProduct_eq_normProduct_of_symmetric
    hc p ell (sixVertexFixedChargeBetheRoots_mem_open hc r k).2.1
    hellrev hunique
  unfold sixVertexFixedOddChargeBetheEigenvalueCandidate
    sixVertexFixedOddChargeBetheEigenvalueValue
    sixVertexZeroPhaseBetheEigenvalueCandidate
    sixVertexZeroPhaseBetheEigenvalueValue
  change (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
      p ell : Complex) * _ = _
  rw [hprod, Complex.ofReal_mul]


theorem sixVertexFixedChargeBetheRoots_zeroPhaseEigenrelation_value_of_odd_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    (sixVertexSectorTransferComplex (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c).mulVec
        (sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc r k)) =
      (sixVertexFixedOddChargeBetheEigenvalueValue hc r k : Complex) •
        sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc r k) := by
  have h :=
    sixVertexFixedChargeBetheRoots_physicalZeroPhaseEigenrelation_of_odd_charge
      hc hr k
  unfold SixVertexCoordinateBetheZeroPhaseEigenrelation at h
  change _ = sixVertexFixedOddChargeBetheEigenvalueCandidate hc r k • _ at h
  rwa [sixVertexFixedOddChargeBetheEigenvalueCandidate_eq_value hc hr k] at h

end
end StatMech.FrontierD
