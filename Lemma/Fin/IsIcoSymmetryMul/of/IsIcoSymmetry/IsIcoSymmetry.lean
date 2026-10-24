import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_EllipticCurve_RubinSilverbergFamily
open RubinSilverberg


private lemma mul_apply_two
  {K : Type*}
  [Field K]
  (g h : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
  (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

private lemma kleinVHom_smul
  {K : Type*}
  [Field K]
  (c n d : K) : kleinVHom (c * n) (c * d) = c ^ 12 * kleinVHom n d := by
  unfold kleinVHom; ring

private lemma kleinVHom_one
  {K : Type*}
  [Field K]
  (u : K) : kleinVHom u 1 = kleinV u := by
  unfold kleinVHom kleinV; ring

private lemma kleinVHom_zero
  {K : Type*}
  [Field K]
  (n : K) : kleinVHom n 0 = 0 := by
  unfold kleinVHom; ring

private lemma moebDen_ne_zero
  {K : Type*}
  [Field K]
  {g : Matrix (Fin 2) (Fin 2) K} (hg : IsIcoSymmetry g) {u : K}
  (hV : kleinV u ≠ 0) : moebDen g u ≠ 0 := by
  intro h0
  have key := hg.2.1 u 1
  rw [mul_one, mul_one, show g 1 0 * u + g 1 1 = moebDen g u from rfl, h0, kleinVHom_zero,
    kleinVHom_one] at key
  exact hV key.symm

private lemma moebDen_mul_moeb
  {K : Type*}
  [Field K]
  {g : Matrix (Fin 2) (Fin 2) K} {u : K} (hd : moebDen g u ≠ 0) :
  moebDen g u * moeb g u = g 0 0 * u + g 0 1 := by
  unfold moeb
  rw [show g 1 0 * u + g 1 1 = moebDen g u from rfl]
  field_simp

private lemma kleinV_moeb
  {K : Type*}
  [Field K]
  {g : Matrix (Fin 2) (Fin 2) K} (hg : IsIcoSymmetry g) {u : K}
  (hV : kleinV u ≠ 0) : moebDen g u ^ 12 * kleinV (moeb g u) = kleinV u := by
  have hd := moebDen_ne_zero hg hV
  have key := hg.2.1 u 1
  rw [mul_one, mul_one, show g 1 0 * u + g 1 1 = moebDen g u from rfl, kleinVHom_one,
    ← moebDen_mul_moeb hd] at key
  rw [← kleinVHom_one, ← key, ← kleinVHom_smul, mul_one]

private lemma kleinV_moeb_ne_zero
  {K : Type*}
  [Field K]
  {g : Matrix (Fin 2) (Fin 2) K} (hg : IsIcoSymmetry g) {u : K}
  (hV : kleinV u ≠ 0) : kleinV (moeb g u) ≠ 0 := by
  intro h0
  have := kleinV_moeb hg hV
  rw [h0, mul_zero] at this
  exact hV this.symm

private lemma moebDen_mul
  {K : Type*}
  [Field K]
  {g h : Matrix (Fin 2) (Fin 2) K} {u : K} (hd : moebDen h u ≠ 0) :
  moebDen (g * h) u = moebDen h u * moebDen g (moeb h u) := by
  have e := moebDen_mul_moeb hd
  unfold moebDen at e ⊢
  rw [mul_apply_two, mul_apply_two]
  linear_combination (-(g 1 0)) * e

private lemma moeb_mul
  {K : Type*}
  [Field K]
  {g h : Matrix (Fin 2) (Fin 2) K} {u : K} (hd : moebDen h u ≠ 0) :
  moeb (g * h) u = moeb g (moeb h u) := by
  have e := moebDen_mul_moeb hd
  have f : moebDen h u = h 1 0 * u + h 1 1 := rfl
  have num : (g * h) 0 0 * u + (g * h) 0 1 = moebDen h u * (g 0 0 * moeb h u + g 0 1) := by
    rw [mul_apply_two, mul_apply_two]
    linear_combination (-(g 0 0)) * e + (-(g 0 1)) * f
  have den : (g * h) 1 0 * u + (g * h) 1 1 = moebDen h u * (g 1 0 * moeb h u + g 1 1) := by
    rw [mul_apply_two, mul_apply_two]
    linear_combination (-(g 1 0)) * e + (-(g 1 1)) * f
  conv_lhs => unfold moeb
  rw [num, den, mul_div_mul_left _ _ hd]
  rfl

private lemma isIcoSymmetry_mul
  {K : Type*}
  [Field K]
  {g h : Matrix (Fin 2) (Fin 2) K} (hg : IsIcoSymmetry g)
  (hh : IsIcoSymmetry h) : IsIcoSymmetry (g * h) := by
  obtain ⟨gdet, gV, gH, gT, gD⟩ := hg
  obtain ⟨hdet, hV', hH, hT, hD⟩ := hh
  have lin : ∀ n d : K, (g * h) 0 0 * n + (g * h) 0 1 * d = g 0 0 * (h 0 0 * n + h 0 1 * d) + g 0 1 * (h 1 0 * n + h 1 1 * d) ∧ (g * h) 1 0 * n + (g * h) 1 1 * d = g 1 0 * (h 0 0 * n + h 0 1 * d) + g 1 1 * (h 1 0 * n + h 1 1 * d) := by
    intro n d
    simp only [mul_apply_two]
    constructor <;> ring
  refine ⟨by rw [Matrix.det_mul, gdet, hdet, mul_one], ?_, ?_, ?_, ?_⟩
  ·
    intro n d; rw [(lin n d).1, (lin n d).2, gV, hV']
  ·
    intro n d; rw [(lin n d).1, (lin n d).2, gH, hH]
  ·
    intro n d; rw [(lin n d).1, (lin n d).2, gT, hT]
  ·
    intro u hVu _
    have hg' : IsIcoSymmetry g := ⟨gdet, gV, gH, gT, gD⟩
    have hh'' : IsIcoSymmetry h := ⟨hdet, hV', hH, hT, hD⟩
    have hdh : moebDen h u ≠ 0 := moebDen_ne_zero hh'' hVu
    have hVv : kleinV (moeb h u) ≠ 0 := kleinV_moeb_ne_zero hh'' hVu
    have hdg : moebDen g (moeb h u) ≠ 0 := moebDen_ne_zero hg' hVv
    obtain ⟨gb, gc⟩ := gD (moeb h u) hVv hdg
    obtain ⟨hb, hc⟩ := hD u hVu hdh
    rw [moebDen_mul hdh, moeb_mul hdh]
    constructor
    ·
      calc
        _ = moebDen h u * (g 0 0 * rsBeta (moeb h u) + g 0 1 * rsGamma (moeb h u)) := by
          rw [mul_assoc, gb]
        _ = g 0 0 * (moebDen h u * rsBeta (moeb h u)) + g 0 1 * (moebDen h u * rsGamma (moeb h u)) := by
          ring
        _ = (g * h) 0 0 * rsBeta u + (g * h) 0 1 * rsGamma u := by
          rw [hb, hc, mul_apply_two, mul_apply_two]; ring
    ·
      calc
        _ = moebDen h u * (g 1 0 * rsBeta (moeb h u) + g 1 1 * rsGamma (moeb h u)) := by
          rw [mul_assoc, gc]
        _ = g 1 0 * (moebDen h u * rsBeta (moeb h u)) + g 1 1 * (moebDen h u * rsGamma (moeb h u)) := by
          ring
        _ = (g * h) 1 0 * rsBeta u + (g * h) 1 1 * rsGamma u := by
          rw [hb, hc, mul_apply_two, mul_apply_two]; ring

open RubinSilverberg in
/--
[RubinSilverberg_IsIcoSymmetry_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RubinSilverberg_IsIcoSymmetry_mul.lean)
-/
@[path]
private lemma main
  [Field K] [CharZero K]
  {g h : Matrix (Fin 2) (Fin 2) K}
-- given
  (hg : IsIcoSymmetry g)
  (hh : IsIcoSymmetry h) :
-- imply
  IsIcoSymmetry (g * h) :=
-- proof
  isIcoSymmetry_mul hg hh


-- created on 2026-10-23
