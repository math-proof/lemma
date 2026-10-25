/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part22


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineFirstEndpointExtend_injective
    (n N : Nat) (start target : IsingLineBox n)
    (htarget : isingLineBoxBoundary n target) :
    Function.Injective (lineFirstEndpointExtend n N start target) := by
  rintro ⟨ar, ap, atail⟩ ⟨br, bp, btail⟩ hab
  have hfull : ap.1 ++ atail.1 = bp.1 ++ btail.1 :=
    congrArg Subtype.val hab
  have hr : (ar : Nat) = br := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbavoid := bp.2.2.2 (ar : Nat) hlt
      apply hbavoid
      have ht := congrArg (fun z : List Bool => z.take (ar : Nat)) hfull
      have haTake : (ap.1 ++ atail.1).take (ar : Nat) = ap.1 := by
        simpa [ap.2.1] using (List.take_left (l₁ := ap.1) (l₂ := atail.1))
      have hbTake : (bp.1 ++ btail.1).take (ar : Nat) =
          bp.1.take (ar : Nat) := by
        apply List.take_append_of_le_length
        rw [bp.2.1]
        omega
      change (ap.1 ++ atail.1).take (ar : Nat) =
        (bp.1 ++ btail.1).take (ar : Nat) at ht
      rw [haTake, hbTake] at ht
      rw [← ht, ap.2.2.1]
      exact htarget
    · have haavoid := ap.2.2.2 (br : Nat) hgt
      apply haavoid
      have ht := congrArg (fun z : List Bool => z.take (br : Nat)) hfull
      have haTake : (ap.1 ++ atail.1).take (br : Nat) =
          ap.1.take (br : Nat) := by
        apply List.take_append_of_le_length
        rw [ap.2.1]
        omega
      have hbTake : (bp.1 ++ btail.1).take (br : Nat) = bp.1 := by
        simpa [bp.2.1] using (List.take_left (l₁ := bp.1) (l₂ := btail.1))
      change (ap.1 ++ atail.1).take (br : Nat) =
        (bp.1 ++ btail.1).take (br : Nat) at ht
      rw [haTake, hbTake] at ht
      rw [ht, bp.2.2.1]
      exact htarget
  have hrSubtype : ar = br := Fin.ext hr
  subst br
  have hpref : ap.1 = bp.1 := by
    have ht := congrArg (fun z : List Bool => z.take (ar : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using ht
  have htail : atail.1 = btail.1 := by
    have hd := congrArg (fun z : List Bool => z.drop (ar : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using hd
  have hap : ap = bp := Subtype.ext hpref
  have hat : atail = btail := Subtype.ext htail
  subst bp
  subst btail
  rfl


theorem lineFirstEndpoint_partial_weight_le_one
    (n N : Nat) (start target : IsingLineBox n)
    (htarget : isingLineBoxBoundary n target) :
    (∑ r ∈ Finset.range (N + 1),
      (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) /
        (2 : Real) ^ r) <= 1 := by
  letI (r : Fin (N + 1)) :
      Fintype (IsingLineFirstEndpointFamily n r start target) :=
    Fintype.ofFinite _
  letI (r : Fin (N + 1)) :
      Fintype {tail : List Bool // tail.length = N - r} :=
    (List.finite_length_eq Bool (N - r)).fintype
  have hcard : Nat.card (LineFirstEndpointExtension n N start target) <=
      Nat.card {bs : List Bool // bs.length = N} :=
    Nat.card_le_card_of_injective
      (lineFirstEndpointExtend n N start target)
      (lineFirstEndpointExtend_injective n N start target htarget)
  have hext : Nat.card (LineFirstEndpointExtension n N start target) =
      ∑ r : Fin (N + 1),
        Nat.card (IsingLineFirstEndpointFamily n r start target) *
          2 ^ (N - (r : Nat)) := by
    unfold LineFirstEndpointExtension
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.card_prod]
    congr 1
    change Nat.card (List.Vector Bool (N - (r : Nat))) =
      2 ^ (N - (r : Nat))
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool (N - (r : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have htargetCard : Nat.card {bs : List Bool // bs.length = N} = 2 ^ N := by
    change Nat.card (List.Vector Bool N) = 2 ^ N
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool N),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hreal :
      (∑ r : Fin (N + 1),
        (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) *
          (2 : Real) ^ (N - (r : Nat))) <= (2 : Real) ^ N := by
    exact_mod_cast (show
      (∑ r : Fin (N + 1),
        Nat.card (IsingLineFirstEndpointFamily n r start target) *
          2 ^ (N - (r : Nat))) <= 2 ^ N by
      rw [← hext, ← htargetCard]
      exact hcard)
  have htwo : 0 < (2 : Real) ^ N := by positivity
  rw [← Fin.sum_univ_eq_sum_range
    (fun r : Nat =>
      (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) /
        (2 : Real) ^ r) (N + 1)]
  calc
    (∑ r : Fin (N + 1),
        (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) /
          (2 : Real) ^ (r : Nat)) =
      (∑ r : Fin (N + 1),
        (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) *
          (2 : Real) ^ (N - (r : Nat))) / (2 : Real) ^ N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      have hrN : (r : Nat) <= N := Nat.le_of_lt_succ r.isLt
      have hpow : (2 : Real) ^ N =
          (2 : Real) ^ (r : Nat) * (2 : Real) ^ (N - (r : Nat)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
    _ <= (2 : Real) ^ N / (2 : Real) ^ N :=
      div_le_div_of_nonneg_right hreal htwo.le
    _ = 1 := by field_simp

theorem orderedFarHorizontalEndpoint_weight_le
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) (hm : 0 < m) (ht : t <= m * m)
    (htarget : isingLineBoxBoundary R target) :
    Nat.card (IsingOrderedFarHorizontalEndpointFamily
        m R t mark target startY targetY) / (4 : Real) ^ t <=
      468 / (m : Real) ^ 2 := by
  let b : Nat -> Real := fun j =>
    Nat.card (IsingLineFarFirstBoundaryFamily m j) / (2 : Real) ^ j
  let a : Nat -> Real := fun r =>
    Nat.card (IsingLineFirstEndpointFamily R r mark target) / (2 : Real) ^ r
  let y : Nat -> Real := fun k =>
    Nat.card (VerticalChoicePathFamily k startY targetY) / (2 : Real) ^ k
  have hb0 (j : Nat) : 0 <= b j := by dsimp [b]; positivity
  have ha0 (r : Nat) : 0 <= a r := by dsimp [a]; positivity
  have hy (k : Nat) : y k <= 2 / Real.sqrt (k + 1 : Real) := by
    dsimp [y]
    rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    let K := isingLineBinomialKernel k startY targetY
    have hK0 : 0 <= K := isingLineBinomialKernel_nonneg _ _ _
    have hrad : 0 <= 2 / (k + 1 : Real) := by positivity
    have hK : K <= Real.sqrt (2 / (k + 1 : Real)) := by
      rw [Real.le_sqrt hK0 hrad]
      exact isingLineBinomialKernel_sq_le k startY targetY
    calc
      K <= Real.sqrt (2 / (k + 1 : Real)) := hK
      _ <= 2 / Real.sqrt (k + 1 : Real) := by
        rw [Real.sqrt_div (by positivity)]
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_iff]
        norm_num
  have hfactor :
      Nat.card (IsingOrderedFarHorizontalEndpointFamily
          m R t mark target startY targetY) / (4 : Real) ^ t =
        ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
          b j * a (k - j) * y k := by
    rw [orderedFarHorizontalEndpoint_weight_eq_sum]
    change (∑ k : Fin (t + 1), ∑ j : Fin k,
      b (j : Nat) * a ((k : Nat) - (j : Nat)) * y (k : Nat)) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun k : Nat => ∑ j : Fin k, b (j : Nat) * a (k - (j : Nat)) * y k)
      (t + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat => b j * a (k - j) * y k) k]
  rw [hfactor]
  calc
    (∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
        b j * a (k - j) * y k) <=
      ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
        b j * a (k - j) *
          (2 / Real.sqrt ((j + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hyjk : y k <= 2 / Real.sqrt ((j + 1 : Nat) : Real) := by
        calc
          y k <= 2 / Real.sqrt (k + 1 : Real) := hy k
          _ <= 2 / Real.sqrt ((j + 1 : Nat) : Real) := by
            apply div_le_div_of_nonneg_left (by norm_num)
              (Real.sqrt_pos.2 (by positivity))
            exact Real.sqrt_le_sqrt (by
              exact_mod_cast (show j + 1 <= k + 1 by omega))
      exact mul_le_mul_of_nonneg_left hyjk
        (mul_nonneg (hb0 j) (ha0 (k - j)))
    _ = ∑ j ∈ Finset.range t,
        b j * (2 / Real.sqrt ((j + 1 : Nat) : Real)) *
          (∑ l ∈ Finset.range (t - j), a (l + 1)) := by
      let f : Nat -> Nat -> Real := fun j l =>
        b j * (2 / Real.sqrt ((j + 1 : Nat) : Real)) * a (l + 1)
      rw [Finset.sum_range_succ']
      simp only [Finset.sum_range_zero, add_zero]
      calc
        (∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
            b j * a (k + 1 - j) *
              (2 / Real.sqrt ((j + 1 : Nat) : Real))) =
          ∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
            f j (k - j) := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro j hj
            have hjk : j <= k := by
              have := Finset.mem_range.mp hj
              omega
            dsimp [f]
            have hidx : k + 1 - j = k - j + 1 := by omega
            rw [hidx]
            ring
        _ = ∑ j ∈ Finset.range t, ∑ l ∈ Finset.range (t - j),
            f j l := Finset.sum_range_diag_flip t f
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [f]
          rw [Finset.mul_sum]
    _ <= ∑ j ∈ Finset.range t,
        b j * (2 / Real.sqrt ((j + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_of_le_one_right
      · exact mul_nonneg (hb0 j) (by positivity)
      · have hmass := lineFirstEndpoint_partial_weight_le_one
          R (t - j) mark target htarget
        have hhead : (∑ l ∈ Finset.range (t - j), a (l + 1)) <=
            ∑ r ∈ Finset.range (t - j + 1), a r := by
          rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right (ha0 0)
        exact hhead.trans (by simpa [a] using hmass)
    _ <= ∑ j ∈ Finset.range (t + 1),
        (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j := by
      calc
        _ = ∑ j ∈ Finset.range t,
            (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ <= _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (by omega)
          · intro j hj hj'
            exact mul_nonneg (by positivity) (hb0 j)
    _ <= 468 / (m : Real) ^ 2 := by
      simpa [b, Nat.cast_add, Nat.cast_one] using
        endpointKernel_farFirstBoundary_sum_le m t hm ht

end
end StatMech.Universality
