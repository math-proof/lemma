/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part24


namespace MetaMathlibExt

lemma r3leg_incidence_sum {p n : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    ∑ y : r3legRepType (p ^ 2 * n),
        Fintype.card {w : r3legIso p // r3legInc hp3 w y} =
      (p ^ 2 - 1) * Nat.threeSquareRepresentationCount n := by
  have hswap := Fintype.card_congr (r3leg_incidenceSwap (n := n) hp3)
  rw [Fintype.card_sigma, Fintype.card_sigma] at hswap
  calc
    ∑ y : r3legRepType (p ^ 2 * n),
        Fintype.card {w : r3legIso p // r3legInc hp3 w y} =
        ∑ w : r3legIso p,
          Fintype.card {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y} := hswap.symm
    _ = ∑ _w : r3legIso p, Nat.threeSquareRepresentationCount n := by
      apply Finset.sum_congr rfl
      intro w _
      exact r3leg_incRep_card hp3 w
    _ = Fintype.card (r3legIso p) * Nat.threeSquareRepresentationCount n := by simp
    _ = (p ^ 2 - 1) * Nat.threeSquareRepresentationCount n := by rw [r3leg_iso_card]

lemma r3leg_quadraticChar_rep {p n : ℕ} [Fact (Nat.Prime p)]
    (x : r3legRepType n) :
    quadraticChar (ZMod p) (-r3legQ (r3legRed p x)) = legendreSym p (-(n : ℤ)) := by
  rw [r3leg_q_red, r3leg_mem_rep.mp x.2]
  simp [legendreSym]

lemma r3leg_zeroRed_filter_card {p n : ℕ} [Fact (Nat.Prime p)] :
    (Finset.univ.filter
      (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0)).card =
      if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0 := by
  rw [← Fintype.card_subtype]
  exact r3leg_zeroRed_rep_card

lemma r3leg_nonzeroRed_filter_card_add {p n : ℕ} [Fact (Nat.Prime p)] :
    (Finset.univ.filter
        (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) ≠ 0)).card +
      (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) =
      Nat.threeSquareRepresentationCount n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0)
  rw [r3leg_zeroRed_filter_card, Finset.card_univ, r3leg_repType_card] at h
  simpa only [ne_eq, add_comm] using h

lemma r3leg_primitive_inc_sum {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) :
    (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
        r3legRed p (y : r3legIntVec) ≠ 0),
      (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
      ((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
        Nat.threeSquareRepresentationCount n) * ((p : ℤ) - 1) := by
  let s := Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
    r3legRed p (y : r3legIntVec) ≠ 0)
  have hcount := r3leg_nonzeroRed_scaled_filter_card_add (p := p) (n := n)
  have hcountz : (s.card : ℤ) + Nat.threeSquareRepresentationCount n =
      Nat.threeSquareRepresentationCount (p ^ 2 * n) := by
    exact_mod_cast hcount
  have hp1 : 1 ≤ p := by omega
  calc
    (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
        r3legRed p (y : r3legIntVec) ≠ 0),
      (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
        ∑ _y ∈ s, ((p - 1 : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyne : r3legRed p (y : r3legIntVec) ≠ 0 := (Finset.mem_filter.mp hy).2
      exact_mod_cast r3leg_primitive_inc_card hp3 y (r3leg_mem_rep.mp y.2) hyne
    _ = (s.card : ℤ) * ((p - 1 : ℕ) : ℤ) := by simp
    _ = (s.card : ℤ) * ((p : ℤ) - 1) := by rw [Nat.cast_sub hp1]; norm_num
    _ = ((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
        Nat.threeSquareRepresentationCount n) * ((p : ℤ) - 1) := by
      rw [show (s.card : ℤ) =
          (Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
            Nat.threeSquareRepresentationCount n by omega]

lemma r3leg_scaled_inc_sum {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) :
    (∑ x : r3legRepType n,
      (Fintype.card
        {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ)) =
      ((Nat.threeSquareRepresentationCount n : ℤ) -
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) *
          ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) +
        (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) *
          ((p : ℤ) ^ 2 - 1) := by
  let f := fun x : r3legRepType n =>
    (Fintype.card
      {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ)
  let r' := if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0
  let s₀ := Finset.univ.filter
    (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0)
  let s₁ := Finset.univ.filter
    (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) ≠ 0)
  have hzeroCard : s₀.card = r' := r3leg_zeroRed_filter_card
  have hnonzeroCard := r3leg_nonzeroRed_filter_card_add (p := p) (n := n)
  have hnonzeroCardz : (s₁.card : ℤ) + (r' : ℤ) =
      Nat.threeSquareRepresentationCount n := by
    exact_mod_cast hnonzeroCard
  have hp2 : 1 ≤ p ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero)
  have hzero : (∑ x ∈ s₀, f x) = (r' : ℤ) * ((p : ℤ) ^ 2 - 1) := by
    calc
      (∑ x ∈ s₀, f x) = ∑ _x ∈ s₀, ((p ^ 2 - 1 : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx0 : r3legRed p (x : r3legIntVec) = 0 := (Finset.mem_filter.mp hx).2
        dsimp [f]
        exact_mod_cast r3leg_scaled_inc_card_of_eq hp3 x hx0
      _ = (s₀.card : ℤ) * ((p ^ 2 - 1 : ℕ) : ℤ) := by simp
      _ = (r' : ℤ) * ((p ^ 2 - 1 : ℕ) : ℤ) := by rw [hzeroCard]
      _ = (r' : ℤ) * ((p : ℤ) ^ 2 - 1) := by
        rw [Nat.cast_sub hp2]
        push_cast
        rfl
  have hnonzero : (∑ x ∈ s₁, f x) =
      ((Nat.threeSquareRepresentationCount n : ℤ) - (r' : ℤ)) *
        ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) := by
    calc
      (∑ x ∈ s₁, f x) =
          ∑ _x ∈ s₁,
            (((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ)))) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxne : r3legRed p (x : r3legIntVec) ≠ 0 := (Finset.mem_filter.mp hx).2
        dsimp [f]
        rw [r3leg_scaled_inc_card_of_ne hp3 x hxne, r3leg_quadraticChar_rep]
      _ = (s₁.card : ℤ) *
          (((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ)))) := by simp
      _ = ((Nat.threeSquareRepresentationCount n : ℤ) - (r' : ℤ)) *
          ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) := by
        rw [show (s₁.card : ℤ) =
            (Nat.threeSquareRepresentationCount n : ℤ) - (r' : ℤ) by omega]
        ring
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0) f
  have hsplit' : (∑ x ∈ s₀, f x) + (∑ x ∈ s₁, f x) = ∑ x, f x := by
    simpa only [s₀, s₁, ne_eq] using hsplit
  change (∑ x, f x) = _
  rw [← hsplit', hzero, hnonzero]
  dsimp [r']
  ring

lemma r3leg_double_count {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) :
    ((p : ℤ) ^ 2 - 1) * Nat.threeSquareRepresentationCount n =
      ((p : ℤ) - 1) *
          ((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
            Nat.threeSquareRepresentationCount n) +
        ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) *
          ((Nat.threeSquareRepresentationCount n : ℤ) -
            (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) +
        ((p : ℤ) ^ 2 - 1) *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) := by
  let f := fun y : r3legRepType (p ^ 2 * n) =>
    (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)
  have hp2 : 1 ≤ p ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero)
  have htotalNat := r3leg_incidence_sum (n := n) hp3
  have htotalCast : (∑ y : r3legRepType (p ^ 2 * n), f y) =
      ((((p ^ 2 - 1) * Nat.threeSquareRepresentationCount n : ℕ) : ℤ)) := by
    dsimp [f]
    exact_mod_cast htotalNat
  have htotal : (∑ y : r3legRepType (p ^ 2 * n), f y) =
      ((p : ℤ) ^ 2 - 1) * Nat.threeSquareRepresentationCount n := by
    rw [htotalCast, Nat.cast_mul, Nat.cast_sub hp2]
    push_cast
    rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun y : r3legRepType (p ^ 2 * n) => r3legRed p (y : r3legIntVec) = 0) f
  have hsplit' :
      (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) = 0), f y) +
        (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) ≠ 0), f y) = ∑ y, f y := by
    simpa only [ne_eq] using hsplit
  calc
    ((p : ℤ) ^ 2 - 1) * Nat.threeSquareRepresentationCount n = ∑ y, f y :=
      htotal.symm
    _ =
        (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) = 0), f y) +
        (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) ≠ 0), f y) := hsplit'.symm
    _ =
        (((Nat.threeSquareRepresentationCount n : ℤ) -
            (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) *
            ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) +
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) *
            ((p : ℤ) ^ 2 - 1)) +
        (((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
            Nat.threeSquareRepresentationCount n) * ((p : ℤ) - 1)) := by
      rw [r3leg_zeroRed_inc_sum hp3, r3leg_scaled_inc_sum hp3,
        r3leg_primitive_inc_sum hp3]
    _ = _ := by ring

lemma r3leg_alpha_one {p n : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) =
      ((p : ℤ) + 1 - legendreSym p (-(n : ℤ))) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) := by
  have hcount := r3leg_double_count (n := n) hp3
  have hleg := r3leg_legendre_mul_correction_eq_zero (p := p) (n := n)
  have hpne : (p : ℤ) - 1 ≠ 0 := by
    have : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
    omega
  apply mul_left_cancel₀ hpne
  nlinarith

end MetaMathlibExt
