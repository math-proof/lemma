import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma rpow_mul_abs_log_pow_le {y δ : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (hδ : 0 < δ) (j : ℕ) : y ^ δ * |Real.log y| ^ j ≤ (((j : ℝ) + 1) / δ) ^ j := by
  have hlog : Real.log y ≤ 0 := Real.log_nonpos hy0.le hy1
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  set s : ℝ := δ * (-Real.log y) / ((j : ℝ) + 1) with hs
  have hs0 : 0 ≤ s := by
    have : 0 ≤ -Real.log y := by linarith
    positivity
  have habs : |Real.log y| = (((j : ℝ) + 1) / δ) * s := by
    rw [abs_of_nonpos hlog, hs]
    field_simp
  have hyδ : y ^ δ = Real.exp (-(((j : ℝ) + 1) * s)) := by
    rw [Real.rpow_def_of_pos hy0]
    congr 1
    rw [hs]
    field_simp
  have hsexp : s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hC : (0 : ℝ) ≤ (((j : ℝ) + 1) / δ) ^ j := by positivity
  calc
    _ = Real.exp (-(((j : ℝ) + 1) * s)) * ((((j : ℝ) + 1) / δ) ^ j * s ^ j) := by
      rw [hyδ, habs, mul_pow]
    _ ≤ Real.exp (-(((j : ℝ) + 1) * s)) * ((((j : ℝ) + 1) / δ) ^ j * Real.exp s ^ j) := by
      gcongr
    _ = (((j : ℝ) + 1) / δ) ^ j * Real.exp (-s) := by
      rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (((j : ℝ) + 1) / δ) ^ j * 1 := by
      gcongr
      apply Real.exp_le_one_iff.mpr (by linarith)
    _ = (((j : ℝ) + 1) / δ) ^ j := mul_one _
private lemma norm_cpow_mul_log_pow_le {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) (μ : ℂ) (hμ : ρ + 2 * δ ≤ μ.re) (j : ℕ) : ‖(y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j‖ ≤ (((j : ℝ) + 1) / δ) ^ j * y ^ (ρ + δ) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  have h1 : y ^ μ.re ≤ y ^ (ρ + 2 * δ) := Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hμ
  have h2 : y ^ (ρ + 2 * δ) = y ^ (ρ + δ) * y ^ δ := by
    rw [show ρ + 2 * δ = (ρ + δ) + δ by ring, Real.rpow_add hy0]
  calc
    _ ≤ y ^ (ρ + 2 * δ) * |Real.log y| ^ j := by
      gcongr
    _ = y ^ (ρ + δ) * (y ^ δ * |Real.log y| ^ j) := by
      rw [h2, mul_assoc]
    _ ≤ y ^ (ρ + δ) * (((j : ℝ) + 1) / δ) ^ j := by
      gcongr
      apply rpow_mul_abs_log_pow_le hy0 hy1 hδ j
    _ = (((j : ℝ) + 1) / δ) ^ j * y ^ (ρ + δ) := mul_comm _ _
private lemma sum_comm_four {α β γ κ N : Type u} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ] [AddCommMonoid N] (g : α → β → γ → κ → N) : ∑ p, ∑ q, ∑ a, ∑ i, g p q a i = ∑ a, ∑ i, ∑ q, ∑ p, g p q a i := calc
  _ = ∑ p, ∑ a, ∑ q, ∑ i, g p q a i := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  _ = ∑ a, ∑ p, ∑ q, ∑ i, g p q a i := Finset.sum_comm
  _ = ∑ a, ∑ p, ∑ i, ∑ q, g p q a i := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  _ = ∑ a, ∑ i, ∑ p, ∑ q, g p q a i := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  _ = ∑ a, ∑ i, ∑ q, ∑ p, g p q a i := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
private lemma fold_sub_reindexed_eq {n J D : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) {E : Type} [AddCommGroup E] [Module ℂ E] (c : ℂ → Fin J → ℂ) (v : Fin D → Fin n → Fin J → E) (sh : Fin D → ℂ) : (∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J, c (e i + sh a) j • v a i j) - ∑ i' : Fin n, ∑ j : Fin J, c (e i') j • (∑ a : Fin D, ∑ i : Fin n, if e i + sh a = e i' then v a i j else 0) = ∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J, if ∃ i', e i' = e i + sh a then (0 : E) else c (e i + sh a) j • v a i j := by
  have hB : (∑ i' : Fin n, ∑ j : Fin J, c (e i') j • (∑ a : Fin D, ∑ i : Fin n, if e i + sh a = e i' then v a i j else 0)) = ∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J, if ∃ i', e i' = e i + sh a then c (e i + sh a) j • v a i j else 0 := calc
    _ = ∑ i' : Fin n, ∑ j : Fin J, ∑ a : Fin D, ∑ i : Fin n, (if e i + sh a = e i' then c (e i') j • v a i j else 0) := by
      refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    _ = ∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J, ∑ i' : Fin n, (if e i + sh a = e i' then c (e i') j • v a i j else 0) := sum_comm_four (fun i' j a i => if e i + sh a = e i' then c (e i') j • v a i j else 0)
    _ = ∑ a : Fin D, ∑ i : Fin n, ∑ j : Fin J, if ∃ i', e i' = e i + sh a then c (e i + sh a) j • v a i j else 0 := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      if h : ∃ i', e i' = e i + sh a then
        obtain ⟨i₀, hi₀⟩ := h
        rw [ite_eq_left ⟨i₀, hi₀⟩, Finset.sum_eq_single i₀]
        ·
          rw [ite_eq_left hi₀.symm, hi₀]
        ·
          intro b _ hb
          rw [ite_eq_right]
          intro hb'
          apply hb (he (hb'.symm.trans hi₀.symm))
        ·
          intro hi₀'
          apply absurd (Finset.mem_univ i₀) hi₀'
      else
        rw [ite_eq_right h]
        refine Finset.sum_eq_zero fun i' _ => ?_
        rw [ite_eq_right]
        intro h'
        apply h ⟨i', h'.symm⟩
  rw [hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp
/--
[RegularSingular_norm_sum_shifted_sub_sum_reindexed_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le.lean)
-/
@[path]
private lemma main
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {n J : ℕ}
  (e : Fin n → ℂ)
  (ρ δ : ℝ)
  (d₂ : ℕ)
  (v : Fin (d₂ + 1) → Fin n → Fin J → E)
  (M y : ℝ)
  -- given
  (he : Function.Injective e)
  (hδ : 0 < δ)
  (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
  (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
  (hM : ∀ a i j, ‖v a i j‖ ≤ M)
  (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
  -- imply
  ‖(∑ a : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) - ∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • (∑ a : Fin (d₂ + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then v a i j else 0)‖ ≤ (((d₂ : ℝ) + 1) * n * M * ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by
  -- proof
  obtain ⟨hy0, hy1⟩ := hy
  have hfold : (∑ a : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) - ∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • (∑ a : Fin (d₂ + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then v a i j else 0) = ∑ a : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J, if ∃ i', e i' = e i + (a : ℕ) then (0 : E) else ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j := fold_sub_reindexed_eq e he (fun μ (j : Fin J) => (y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) v (fun a : Fin (d₂ + 1) => ((a : ℕ) : ℂ))
  rw [hfold]
  have hterm : ∀ (a : Fin (d₂ + 1)) (i : Fin n) (j : Fin J), ‖(if ∃ i', e i' = e i + (a : ℕ) then (0 : E) else ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j)‖ ≤ M * ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ) := by
    intro a i j
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a i j)
    split_ifs with h
    ·
      rw [norm_zero]
      positivity
    ·
      have hre : ρ + 2 * δ ≤ (e i + ((a : ℕ) : ℂ)).re := by
        apply hgap i (a : ℕ)
        by_contra hle
        apply h (hcl i (a : ℕ) (not_lt.mp hle))
      rw [norm_smul]
      calc
        _ ≤ (((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ)) * M := by
          gcongr ?_ * ?_
          · apply norm_cpow_mul_log_pow_le hy0 hy1 hδ ρ _ hre (j : ℕ)
          · apply hM a i j
        _ = M * ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ) := by ring
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm a i j).trans ?_
  have hj : ∑ j : Fin J, M * ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ) = M * (∑ j : Fin J, ((((j : ℕ) : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hj, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  apply le_of_eq
  ring


-- created on 2026-10-20
