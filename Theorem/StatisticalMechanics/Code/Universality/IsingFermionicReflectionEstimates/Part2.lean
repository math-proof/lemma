/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part3


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem isingLineBinomialKernel_eq_natCard_verticalChoicePath_div
    (t : Nat) (x y : Int) :
    isingLineBinomialKernel t x y =
      Nat.card (VerticalChoicePathFamily t x y) / (2 : Real) ^ t := by
  induction t generalizing x with
  | zero =>
      by_cases hxy : x = y
      · subst y
        rw [Nat.card_congr (verticalChoicePathFamilyZeroSelfEquiv x)]
        simp [isingLineBinomialKernel, isingBinomialWeight]
      · rw [Nat.card_congr
          (verticalChoicePathFamilyZeroNeEquiv x y hxy)]
        simp [isingLineBinomialKernel, isingBinomialWeight, hxy,
          Ne.symm hxy]
  | succ t ih =>
      rw [isingLineBinomialKernel_succ]
      rw [Nat.card_congr (verticalChoicePathFamilySuccEquiv t x y),
        Nat.card_sigma]
      rw [ih, ih]
      simp
      push_cast
      rw [pow_succ]
      ring

theorem intLineChoiceRun_of_zero (n : Nat) (bs : List Bool) :
    intLineChoiceRun n 0 bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [intLineChoiceRun, intLineChoiceNext, ih]

theorem intLineChoiceRun_eq_zero_of_free_hit
    (n : Nat) (start : Int) (bs : List Bool) (k : Nat)
    (hstart0 : 0 ≤ start) (hstartn : start < n)
    (hk : k ≤ bs.length)
    (hhit : lineFreeEndpoint start (bs.take k) = 0)
    (hnoRight : ∀ j, j < k →
      lineFreeEndpoint start (bs.take j) ≠ n) :
    intLineChoiceRun n start bs = 0 := by
  induction k generalizing start bs with
  | zero =>
      simp [lineFreeEndpoint] at hhit
      subst start
      exact intLineChoiceRun_of_zero n bs
  | succ k ih =>
      cases bs with
      | nil => simp at hk
      | cons b bs =>
          have hstartNeN : start ≠ n := hnoRight 0 (by omega)
          by_cases hstartZero : start = 0
          · subst start
            exact intLineChoiceRun_of_zero n (b :: bs)
          · have hstartPos : 0 < start := by omega
            let next := start + if b then 1 else -1
            have hrun : intLineChoiceRun n start (b :: bs) =
                intLineChoiceRun n next bs := by
              simp [intLineChoiceRun, intLineChoiceNext, hstartZero,
                hstartNeN, next]
            by_cases hnextZero : next = 0
            · rw [hrun, hnextZero]
              exact intLineChoiceRun_of_zero n bs
            · have hhitTail : lineFreeEndpoint next (bs.take k) = 0 := by
                simpa [lineFreeEndpoint, next] using hhit
              have hkTail : k ≤ bs.length := by simpa using hk
              have hnextNonneg : 0 ≤ next := by
                unfold next
                cases b <;> simp_all <;> omega
              have hnextLt : next < n := by
                by_contra hnot
                have hnle : n ≤ next := by omega
                have hnextLe : next ≤ n := by
                  unfold next
                  cases b <;> simp_all <;> omega
                have hnextEq : next = n := by omega
                by_cases hk0 : k = 0
                · subst k
                  simp [lineFreeEndpoint] at hhitTail
                  exact hnextZero hhitTail
                · have hbad := hnoRight 1 (by omega)
                  apply hbad
                  simpa [lineFreeEndpoint, next, hnextEq]
              have hnoTail : ∀ j, j < k →
                  lineFreeEndpoint next (bs.take j) ≠ n := by
                intro j hj
                have hbad := hnoRight (j + 1) (by omega)
                simpa [lineFreeEndpoint, next, List.take_succ_cons] using hbad
              rw [hrun]
              exact ih next bs hnextNonneg hnextLt hkTail hhitTail hnoTail

theorem intLineChoiceRun_eq_lineChoiceRun_val
    (n : Nat) (p : IsingLineBox n) (bs : List Bool) :
    intLineChoiceRun n p.1 bs = (isingLineChoiceRun n p bs).1 := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
      simp only [intLineChoiceRun, isingLineChoiceRun]
      by_cases hp : isingLineBoxBoundary n p
      · have hp' : (p.1 : Int) = 0 ∨ (p.1 : Int) = n := by
          unfold isingLineBoxBoundary at hp
          rcases hp with hp | hp <;> simp [hp]
        simp only [intLineChoiceNext, hp', if_pos,
          isingLineChoiceNext, dif_pos hp]
        exact ih p
      · have hp' : ¬((p.1 : Int) = 0 ∨ (p.1 : Int) = n) := by
          unfold isingLineBoxBoundary at hp
          push Not at hp ⊢
          exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩
        simp only [intLineChoiceNext, hp', if_false,
          isingLineChoiceNext, dif_neg hp]
        cases b
        · have hnext := ih (isingLineWest n p)
          have hp0 : 0 < p.1 := by
            unfold isingLineBoxBoundary at hp
            omega
          have hcast : ((isingLineWest n p).1 : Int) = (p.1 : Int) - 1 := by
            change ((p.1 - 1 : Nat) : Int) = _
            rw [Int.ofNat_sub hp0]
            norm_num
          change intLineChoiceRun n ((p.1 : Int) - 1) bs = _
          rw [← hcast]
          exact hnext
        · have hnext := ih (isingLineEast n p hp)
          simpa [isingLineEast] using hnext

theorem encodeStep_injective_of_valid {d e : Int × Int}
    (hd : (d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 1 ∨ d.2 = -1))
    (he : (e.1 = 1 ∨ e.1 = -1) ∧ (e.2 = 1 ∨ e.2 = -1))
    (h : encodeStep d = encodeStep e) : d = e := by
  rcases hd with ⟨hdx | hdx, hdy | hdy⟩ <;>
    rcases he with ⟨hex | hex, hey | hey⟩ <;>
    simp [encodeStep, hdx, hdy, hex, hey] at h
  all_goals apply Prod.ext <;> simp_all

theorem encodePath_injective_of_valid
    {a b : List (Int × Int)}
    (ha : IsingDiagonalWalkStepsValid a)
    (hb : IsingDiagonalWalkStepsValid b)
    (h : encodePath a = encodePath b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons e b => simp [encodePath] at h
  | cons d a ih =>
      cases b with
      | nil => simp [encodePath] at h
      | cons e b =>
          simp only [encodePath, List.map_cons, List.cons.injEq] at h
          have hd := ha d (by simp)
          have he := hb e (by simp)
          have hde := encodeStep_injective_of_valid hd he h.1
          subst e
          congr 1
          apply ih
          · intro z hz
            exact ha z (by simp [hz])
          · intro z hz
            exact hb z (by simp [hz])
          · exact h.2

end IsingDiagonalWalkHitSplit
end StatMech.Universality
