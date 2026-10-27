import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero.lean)
-/
@[path]
private lemma main
  (W : Type) [CommRing W] [IsDomain W]
  (π : W)
  (hπ : π ≠ 0)
  (f u v : MvPowerSeries (Fin 2) W)
  (hv : IsUnit v)
  (hf : MvPowerSeries.coeff (0 : Finsupp (Fin 2) ℕ) f = 0)
  (e : ℕ)
  (g g₁ r : MvPowerSeries (Fin 2) W)
  (hg : ∀ n : Finsupp (Fin 2) ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0)
  (hg₁ : ∀ n : Finsupp (Fin 2) ℕ, n 0 + n 1 < e + 1 → MvPowerSeries.coeff n g₁ = 0)
  (hrel : g = g₁ + (MvPowerSeries.C π * v - f * u) * r)
  (n : Finsupp (Fin 2) ℕ)
  (hn : n 0 + n 1 = e) :
  -- imply
  MvPowerSeries.coeff n g ∈ Ideal.span {π} := by
  -- proof
  classical
  let P : ℕ → MvPowerSeries (Fin 2) W → Prop := fun d a => ∀ m : Finsupp (Fin 2) ℕ, m 0 + m 1 < d → MvPowerSeries.coeff m a = 0
  have hmul : ∀ d d' (a b : MvPowerSeries (Fin 2) W), P d a → P d' b → P (d + d') (a * b) := by
    intro d d' a b ha hb m hm
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h0 : p.1 0 + p.2 0 = m 0 := by
      rw [← Finsupp.add_apply, hp]
    have h1 : p.1 1 + p.2 1 = m 1 := by
      rw [← Finsupp.add_apply, hp]
    if hlt : p.1 0 + p.1 1 < d then
      rw [ha p.1 hlt, zero_mul]
    else
      have : p.2 0 + p.2 1 < d' := by
        omega
      rw [hb p.2 this, mul_zero]
  have hP0 : ∀ a : MvPowerSeries (Fin 2) W, P 0 a := fun a m hm => by omega
  have hPf : P 1 f := by
    intro m hm
    have : m = 0 := by
      ext j
      fin_cases j
      ·
        simp
        omega
      ·
        simp
        omega
    rw [this]
    apply hf
  have hmulL : ∀ d (a b : MvPowerSeries (Fin 2) W), P d b → P d (a * b) := by
    intro d a b hb
    have := hmul 0 d a b (hP0 a) hb
    rwa [zero_add] at this
  have hmul1 : ∀ d (b : MvPowerSeries (Fin 2) W), P d b → P (d + 1) (f * b) := by
    intro d b hb
    have := hmul 1 d f b hPf hb
    rwa [add_comm] at this
  obtain ⟨vU, rfl⟩ := hv
  set s : MvPowerSeries (Fin 2) W := (vU : MvPowerSeries (Fin 2) W) * r with hs
  have hr : r = ((vU⁻¹ : Units (MvPowerSeries (Fin 2) W)) : MvPowerSeries (Fin 2) W) * s := by
    rw [hs, ← mul_assoc, Units.inv_mul, one_mul]
  have hcoef : ∀ m : Finsupp (Fin 2) ℕ, MvPowerSeries.coeff m g = MvPowerSeries.coeff m g₁ + (π * MvPowerSeries.coeff m s - MvPowerSeries.coeff m (f * (u * (((vU⁻¹ : Units (MvPowerSeries (Fin 2) W)) : MvPowerSeries (Fin 2) W) * s)))) := by
    intro m
    rw [hrel, map_add, sub_mul, map_sub, mul_assoc, MvPowerSeries.coeff_C_mul, ← hs, mul_assoc, ← hr]
  have hPs : ∀ d, d ≤ e → P d s := by
    intro d
    induction d
    ·
      intro _
      apply hP0 s
    ·
      rename_i d ih
      intro hd m hm
      have ih' := ih (by omega)
      obtain hlt | _ := Nat.lt_or_ge (m 0 + m 1) d
      · apply ih' m hlt
      ·
        have hfur : MvPowerSeries.coeff m (f * (u * (((vU⁻¹ : Units (MvPowerSeries (Fin 2) W)) : MvPowerSeries (Fin 2) W) * s))) = 0 := by
          apply hmul1 d _ (hmulL d u _ (hmulL d _ s ih')) m (by omega)
        have h := hcoef m
        rw [hg m (by omega), hg₁ m (by omega), hfur, sub_zero, zero_add] at h
        have : π * MvPowerSeries.coeff m s = 0 := h.symm
        obtain h0 | h0 := Iff.mp mul_eq_zero this
        · apply absurd h0 hπ
        · apply h0
  have hfur : MvPowerSeries.coeff n (f * (u * (((vU⁻¹ : Units (MvPowerSeries (Fin 2) W)) : MvPowerSeries (Fin 2) W) * s))) = 0 := by
    apply hmul1 e _ (hmulL e u _ (hmulL e _ s (hPs e le_rfl))) n (by omega)
  rw [hcoef n, hg₁ n (by omega), hfur, sub_zero, zero_add]
  apply Iff.mpr Ideal.mem_span_singleton (dvd_mul_right π _)


-- created on 2026-10-20
