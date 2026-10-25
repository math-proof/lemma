/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem farFirstBoundaryExtend_injective (m K : Nat) :
    Function.Injective (farFirstBoundaryExtend m K) := by
  rintro ⟨aj, ap, atail⟩ ⟨bj, bp, btail⟩ hab
  have hfull : ap.1 ++ atail.1 = bp.1 ++ btail.1 :=
    congrArg Subtype.val hab
  have hj : (aj : Nat) = bj := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbavoid := bp.2.2.2 (aj : Nat) hlt
      apply hbavoid
      have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
      change (ap.1 ++ atail.1).take (aj : Nat) =
        (bp.1 ++ btail.1).take (aj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (aj : Nat) = ap.1 := by
        simpa [ap.2.1] using
          (List.take_left (l₁ := ap.1) (l₂ := atail.1))
      have hbTake : (bp.1 ++ btail.1).take (aj : Nat) =
          bp.1.take (aj : Nat) := by
        apply List.take_append_of_le_length
        rw [bp.2.1]
        omega
      rw [haTake, hbTake] at ht
      rw [← ht, ap.2.2.1]
      simp [isingLineBoxBoundary]
    · have haavoid := ap.2.2.2 (bj : Nat) hgt
      apply haavoid
      have ht := congrArg (fun z : List Bool => z.take (bj : Nat)) hfull
      change (ap.1 ++ atail.1).take (bj : Nat) =
        (bp.1 ++ btail.1).take (bj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (bj : Nat) =
          ap.1.take (bj : Nat) := by
        apply List.take_append_of_le_length
        rw [ap.2.1]
        omega
      have hbTake : (bp.1 ++ btail.1).take (bj : Nat) = bp.1 := by
        simpa [bp.2.1] using
          (List.take_left (l₁ := bp.1) (l₂ := btail.1))
      rw [haTake, hbTake] at ht
      rw [ht, bp.2.2.1]
      simp [isingLineBoxBoundary]
  have hjSubtype : aj = bj := Fin.ext hj
  subst bj
  have hpref : ap.1 = bp.1 := by
    have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using ht
  have htail : atail.1 = btail.1 := by
    have hd := congrArg (fun z : List Bool => z.drop (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using hd
  have hap : ap = bp := Subtype.ext hpref
  have hat : atail = btail := Subtype.ext htail
  subst bp
  subst btail
  rfl


theorem lineFarFirstBoundary_partial_weight_le_fifth
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤
      26 * (K + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
  have hcard : Nat.card (FarFirstBoundaryExtension m K) ≤
      Nat.card (IsingLineChoicePathFamily m K
        ⟨m - 1, by omega⟩ ⟨0, by omega⟩) :=
    Nat.card_le_card_of_injective (farFirstBoundaryExtend m K)
      (farFirstBoundaryExtend_injective m K)
  have hext : Nat.card (FarFirstBoundaryExtension m K) =
      ∑ j : Fin (K + 1),
        Nat.card (IsingLineFarFirstBoundaryFamily m j) * 2 ^ (K - j) := by
    letI (j : Fin (K + 1)) :
        Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (K + 1)) :
        Fintype {tail : List Bool // tail.length = K - j} :=
      (List.finite_length_eq Bool (K - j)).fintype
    change Nat.card (Σ j : Fin (K + 1),
      IsingLineFarFirstBoundaryFamily m j ×
        {tail : List Bool // tail.length = K - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.card_prod]
    congr 1
    change Nat.card (List.Vector Bool (K - (j : Nat))) = 2 ^ (K - (j : Nat))
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool (K - (j : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hweightedNat :
      (∑ j : Fin (K + 1),
        Nat.card (IsingLineFarFirstBoundaryFamily m j) * 2 ^ (K - j)) ≤
          Nat.card (IsingLineChoicePathFamily m K
            ⟨m - 1, by omega⟩ ⟨0, by omega⟩) := by
    rw [← hext]
    exact hcard
  have hweightedReal :
      (∑ j : Fin (K + 1),
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) ≤
          (Nat.card (IsingLineChoicePathFamily m K
            ⟨m - 1, by omega⟩ ⟨0, by omega⟩) : Real) := by
    exact_mod_cast hweightedNat
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
      (2 : Real) ^ (K - j)) (K + 1)] at hweightedReal
  have htwo : 0 < (2 : Real) ^ K := by positivity
  have hdiv := div_le_div_of_nonneg_right hweightedReal htwo.le
  calc
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) =
      (∑ j ∈ Finset.range (K + 1),
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) / (2 : Real) ^ K := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := by
        have := Finset.mem_range.mp hj
        omega
      have hpow : (2 : Real) ^ K =
          (2 : Real) ^ j * (2 : Real) ^ (K - j) := by
        calc
          (2 : Real) ^ K = (2 : Real) ^ (j + (K - j)) := by
            congr 1
            omega
          _ = _ := pow_add _ _ _
      calc
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) /
            (2 : Real) ^ j =
          ((Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
            (2 : Real) ^ (K - j)) /
              ((2 : Real) ^ j * (2 : Real) ^ (K - j)) :=
            (mul_div_mul_right _ _ (by positivity)).symm
        _ = _ := by rw [hpow]
    _ ≤ (Nat.card (IsingLineChoicePathFamily m K
        ⟨m - 1, by omega⟩ ⟨0, by omega⟩) : Real) /
          (2 : Real) ^ K := hdiv
    _ = isingLineStoppedKernel m K
        ⟨m - 1, by omega⟩ ⟨0, by omega⟩ := by
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div]
    _ ≤ 26 * (K + 1 : Real) ^ 2 / (m : Real) ^ 5 :=
      isingLineStoppedKernel_far_boundary_le_fifth m K hm

theorem two_inv_sqrt_diff_mul_sq_le_sqrt (k : Nat) :
    (2 / Real.sqrt (k + 1 : Real) -
        2 / Real.sqrt (k + 2 : Real)) * (k + 1 : Real) ^ 2 ≤
      Real.sqrt (k + 1 : Real) := by
  let x := Real.sqrt (k + 1 : Real)
  let y := Real.sqrt (k + 2 : Real)
  have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
  have hy : 0 < y := Real.sqrt_pos.2 (by positivity)
  have hx2 : x ^ 2 = (k + 1 : Real) := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hy2 : y ^ 2 = (k + 2 : Real) := by
    dsimp [y]
    rw [Real.sq_sqrt]
    positivity
  have hxy : x ≤ y := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hden : 0 < y * (y + x) := mul_pos hy (add_pos hy hx)
  have heq :
      (2 / x - 2 / y) * (k + 1 : Real) ^ 2 =
        2 * x ^ 3 / (y * (y + x)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    nlinarith [hx2, hy2]
  change (2 / x - 2 / y) * (k + 1 : Real) ^ 2 ≤ x
  rw [heq]
  apply (div_le_iff₀ hden).2
  have hxx : x ^ 2 ≤ x * y := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hxy)]
  have hsum : 2 * x ≤ y + x := by linarith
  have hmul := mul_le_mul hxx hsum (by positivity) (by positivity)
  nlinarith


theorem endpointKernel_farFirstBoundary_sum_le
    (m N : Nat) (hm : 0 < m) (hN : N ≤ m * m) :
    (∑ k ∈ Finset.range (N + 1),
      (2 / Real.sqrt (k + 1 : Real)) *
        ((Nat.card (IsingLineFarFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) ≤
      468 / (m : Real) ^ 2 := by
  let a : Nat → Real := fun k => 2 / Real.sqrt (k + 1 : Real)
  let b : Nat → Real := fun k =>
    (Nat.card (IsingLineFarFirstBoundaryFamily m k) : Real) / (2 : Real) ^ k
  have hm2 : 0 < (m : Real) ^ 2 := by positivity
  have hm5 : 0 < (m : Real) ^ 5 := by positivity
  have hNReal : (N : Real) ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show N ≤ m ^ 2 by simpa [pow_two] using hN)
  have hpartial (k : Nat) :
      (∑ j ∈ Finset.range (k + 1), b j) ≤
        26 * (k + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
    simpa [b] using lineFarFirstBoundary_partial_weight_le_fifth m k hm
  have hA (k : Nat) (hk : k ≤ N) :
      (k + 1 : Real) ≤ 4 * (m : Real) ^ 2 := by
    have hkReal : (k : Real) ≤ (m : Real) ^ 2 :=
      le_trans (by exact_mod_cast hk) hNReal
    have hmOne : (1 : Real) ≤ (m : Real) ^ 2 := by
      have : (1 : Nat) ≤ m := hm
      nlinarith [show (1 : Real) ≤ m by exact_mod_cast this]
    nlinarith
  have hsqrt (k : Nat) (hk : k ≤ N) :
      Real.sqrt (k + 1 : Real) ≤ 2 * (m : Real) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have := hA k hk
      nlinarith
  have hlast :
      a N * (∑ k ∈ Finset.range (N + 1), b k) ≤
        416 / (m : Real) ^ 2 := by
    calc
      _ ≤ a N * (26 * (N + 1 : Real) ^ 2 / (m : Real) ^ 5) := by
        apply mul_le_mul_of_nonneg_left (hpartial N)
        dsimp [a]
        positivity
      _ ≤ 416 / (m : Real) ^ 2 := by
        dsimp [a]
        let x := Real.sqrt (N + 1 : Real)
        have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
        have hx2 : x ^ 2 = (N + 1 : Real) := by
          dsimp [x]
          rw [Real.sq_sqrt]
          positivity
        have hA' := hA N (le_refl _)
        have hx' := hsqrt N (le_refl _)
        change (2 / x) * (26 * (N + 1 : Real) ^ 2 / (m : Real) ^ 5) ≤
          416 / (m : Real) ^ 2
        have hprod : (N + 1 : Real) * x ≤ 8 * (m : Real) ^ 3 := by
          have := mul_le_mul hA' hx' (Real.sqrt_nonneg _) (by positivity)
          nlinarith
        have hprod26 := mul_le_mul_of_nonneg_left hprod
          (show (0 : Real) ≤ 52 by norm_num)
        have hprod26' : 52 * ((N + 1 : Real) * x) ≤
            416 * (m : Real) ^ 3 := by
          convert hprod26 using 1 <;> ring
        calc
          (2 / x) * (26 * (N + 1 : Real) ^ 2 / (m : Real) ^ 5) =
              52 * ((N + 1 : Real) * x) / (m : Real) ^ 5 := by
            field_simp [ne_of_gt hx]
            nlinarith [hx2]
          _ ≤ 416 * (m : Real) ^ 3 / (m : Real) ^ 5 :=
            div_le_div_of_nonneg_right hprod26' hm5.le
          _ = 416 / (m : Real) ^ 2 := by field_simp
  have hterm (k : Nat) :
      (a k - a (k + 1)) *
          (∑ j ∈ Finset.range (k + 1), b j) ≤
        26 * Real.sqrt (k + 1 : Real) / (m : Real) ^ 5 := by
    have hdiff : 0 ≤ a k - a (k + 1) := by
      dsimp [a]
      apply sub_nonneg.mpr
      apply div_le_div_of_nonneg_left (by norm_num)
        (Real.sqrt_pos.2 (by positivity))
      exact Real.sqrt_le_sqrt (by norm_num)
    calc
      _ ≤ (a k - a (k + 1)) *
          (26 * (k + 1 : Real) ^ 2 / (m : Real) ^ 5) :=
        mul_le_mul_of_nonneg_left (hpartial k) hdiff
      _ ≤ 26 * Real.sqrt (k + 1 : Real) / (m : Real) ^ 5 := by
        dsimp [a]
        rw [show (((k + 1 : Nat) : Real) + 1) = (k : Real) + 2 by
          push_cast
          ring]
        have hcore := two_inv_sqrt_diff_mul_sq_le_sqrt k
        have hcore26 := mul_le_mul_of_nonneg_left hcore
          (show (0 : Real) ≤ 26 by norm_num)
        calc
          (2 / Real.sqrt (k + 1 : Real) -
              2 / Real.sqrt (k + 2 : Real)) *
                (26 * (k + 1 : Real) ^ 2 / (m : Real) ^ 5) =
            (26 * ((2 / Real.sqrt (k + 1 : Real) -
              2 / Real.sqrt (k + 2 : Real)) *
                (k + 1 : Real) ^ 2)) / (m : Real) ^ 5 := by ring
          _ ≤ (26 * Real.sqrt (k + 1 : Real)) / (m : Real) ^ 5 :=
            div_le_div_of_nonneg_right hcore26 hm5.le
  rw [show (∑ k ∈ Finset.range (N + 1),
      (2 / Real.sqrt (k + 1 : Real)) *
        ((Nat.card (IsingLineFarFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) =
      ∑ k ∈ Finset.range (N + 1), a k * b k by rfl]
  rw [endpointRace_sum_mul_eq_last_partial_add]
  calc
    _ ≤ 416 / (m : Real) ^ 2 +
        ∑ k ∈ Finset.range N,
          26 * Real.sqrt (k + 1 : Real) / (m : Real) ^ 5 := by
      exact add_le_add hlast (Finset.sum_le_sum fun k hk => hterm k)
    _ ≤ 416 / (m : Real) ^ 2 +
        (N : Real) * (52 * (m : Real) / (m : Real) ^ 5) := by
      apply add_le_add (le_refl _)
      calc
        _ ≤ ∑ k ∈ Finset.range N,
            52 * (m : Real) / (m : Real) ^ 5 := by
          apply Finset.sum_le_sum
          intro k hk
          have hkN : k ≤ N := (Finset.mem_range.mp hk).le
          apply div_le_div_of_nonneg_right _ hm5.le
          have := hsqrt k hkN
          nlinarith
        _ = (N : Real) * (52 * (m : Real) / (m : Real) ^ 5) := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
    _ ≤ 416 / (m : Real) ^ 2 + 52 / (m : Real) ^ 2 := by
      apply add_le_add (le_refl _)
      calc
        (N : Real) * (52 * (m : Real) / (m : Real) ^ 5) ≤
            (m : Real) ^ 2 * (52 * (m : Real) / (m : Real) ^ 5) :=
          mul_le_mul_of_nonneg_right hNReal (by positivity)
        _ = 52 / (m : Real) ^ 2 := by field_simp
    _ = 468 / (m : Real) ^ 2 := by ring


end
end StatMech.Universality
