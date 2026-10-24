import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt.lean)
-/
@[path]
private lemma main
  (W : Type) [CommRing W] (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
  -- imply
  g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e ↔
    ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0 := by
  -- proof
  classical
  set N : Ideal (MvPowerSeries (Fin 2) W) :=
    Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} with hN
  let P : ℕ → MvPowerSeries (Fin 2) W → Prop := fun d a => ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < d → MvPowerSeries.coeff n a = 0
  have hmul : ∀ d d' (a b : MvPowerSeries (Fin 2) W), P d a → P d' b → P (d + d') (a * b) := by
    intro d d' a b ha hb n hn
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h0 : p.1 0 + p.2 0 = n 0 := by rw [← Finsupp.add_apply, hp]
    have h1 : p.1 1 + p.2 1 = n 1 := by rw [← Finsupp.add_apply, hp]
    if hlt : p.1 0 + p.1 1 < d then
      rw [ha p.1 hlt, zero_mul]
    else
      have : p.2 0 + p.2 1 < d' := by omega
      rw [hb p.2 this, mul_zero]
  have hadd : ∀ d (a b : MvPowerSeries (Fin 2) W), P d a → P d b → P d (a + b) := by
    intro d a b ha hb n hn
    rw [map_add, ha n hn, hb n hn, add_zero]
  have hzero : ∀ d, P d 0 := fun d n _ => by simp
  have hX : ∀ i : Fin 2, P 1 (MvPowerSeries.X i) := by
    intro i n hn
    have : n = 0 := by
      ext j
      fin_cases j
      ·
        simp
        omega
      ·
        simp
        omega
    rw [this, MvPowerSeries.coeff_zero_X]
  have hN1 : ∀ b ∈ N, P 1 b := by
    intro b hb
    rw [hN] at hb
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    ·
      intro x hx
      obtain rfl | rfl := hx
      · apply hX 0
      · apply hX 1
    · apply hzero 1
    ·
      intro x y _ _ hx hy
      apply hadd 1 x y hx hy
    ·
      intro r x _ hx
      have := hmul 0 1 r x (fun n hn => by omega) hx
      simp at this
      apply this
  have hpow : ∀ d, ∀ a ∈ N ^ d, P d a := by
    intro d
    induction d
    ·
      intro a _ n hn
      omega
    ·
      rename_i d ih
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      ·
        intro x hx y hy
        apply hmul d 1 x y (ih x hx) (hN1 y hy)
      ·
        intro x y hx hy
        apply hadd _ x y hx hy
  constructor
  · apply hpow e g
  ·
    intro hg
    let α : ℕ → (Fin 2 →₀ ℕ) := fun i => Finsupp.single 0 i + Finsupp.single 1 (e - i)
    let gi : ℕ → MvPowerSeries (Fin 2) W := fun i =>
      fun γ => if min ((γ + α i) 0) e = i then MvPowerSeries.coeff (γ + α i) g else 0
    have hgi : ∀ (i : ℕ) (γ : Fin 2 →₀ ℕ), MvPowerSeries.coeff γ (gi i) =
        if min ((γ + α i) 0) e = i then MvPowerSeries.coeff (γ + α i) g else 0 := fun i γ => rfl
    have hdecomp : g = ∑ i ∈ Finset.range (e + 1), MvPowerSeries.monomial (α i) 1 * gi i := by
      ext β
      rw [map_sum]
      simp only [MvPowerSeries.coeff_monomial_mul, one_mul]
      if hβ : e ≤ β 0 + β 1 then
        rw [Finset.sum_eq_single (min (β 0) e)]
        ·
          have hle : α (min (β 0) e) ≤ β := by
            intro j
            fin_cases j
            · simp [α]
            ·
              simp [α]
              omega
          rw [ite_eq_left hle, hgi, tsub_add_cancel_of_le hle, ite_eq_left rfl]
        ·
          intro i hi hne
          if hle : α i ≤ β then
            rw [ite_eq_left hle, hgi, tsub_add_cancel_of_le hle, ite_eq_right (Ne.symm hne)]
          else
            rw [ite_eq_right hle]
        ·
          intro h
          exfalso
          apply h
          simp only [Finset.mem_range]
          omega
      else
        push Not at hβ
        rw [hg β hβ]
        symm
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [ite_eq_right]
        intro hle
        have h0 := hle 0
        have h1 := hle 1
        simp only [α, Finsupp.add_apply, Finsupp.single_apply] at h0 h1
        simp at h0 h1
        simp only [Finset.mem_range] at hi
        omega
    rw [hdecomp]
    refine Ideal.sum_mem _ fun i hi => ?_
    apply Ideal.mul_mem_right
    have hmon : MvPowerSeries.monomial (α i) (1 : W) =
        (MvPowerSeries.X 0) ^ i * (MvPowerSeries.X 1) ^ (e - i) := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
    rw [hmon]
    simp only [Finset.mem_range] at hi
    have h1 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ^ i ∈ N ^ i :=
      Ideal.pow_mem_pow (Ideal.subset_span (by simp)) i
    have h2 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ^ (e - i) ∈ N ^ (e - i) :=
      Ideal.pow_mem_pow (Ideal.subset_span (by simp)) (e - i)
    have := Ideal.mul_mem_mul h1 h2
    rwa [← pow_add, show i + (e - i) = e by omega] at this


-- created on 2026-10-20
