import Lemma.LpSpace.HalfSq.le.AddAddHalfSqInner_MulSub1HalfSqSub.of.All_Ne_0.Gt_2
import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
open Finset LpSpace Real Set Filter Topology


@[main]
private lemma main
  {p d : ℕ}
  {x y : LpSpace p d}
-- given
  (h : 2 ≤ p) :
-- imply
  half_sq y ≤ half_sq x + inner ℝ (half_sq' x).toL2 (y - x).toL2 + (p - 1) * half_sq (y - x) := by
-- proof
  if hp : p = 2 then
    subst hp
    have hn : ∀ z : LpSpace 2 d, ‖z‖ = ‖z.toL2‖ := fun z => by
      rw [PiLp.norm_eq_sum (by simp) z, EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
      simp [toL2]
    have hg : (half_sq' x).toL2 = x.toL2 := by
      ext i
      simp [half_sq', toL2]
    have ht : (y - x).toL2 = y.toL2 - x.toL2 := by
      ext i
      simp [toL2]
    have hid := norm_add_sq_real x.toL2 (y.toL2 - x.toL2)
    rw [add_sub_cancel] at hid
    simp only [half_sq]
    rw [hn y, hn x, hn (y - x), hg, ht]
    push_cast
    linarith
  else
    have h₀ : 2 < p := by omega
    have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (by omega : 1 ≤ p)⟩
    have hp' : (2 : ℝ) < p := by exact_mod_cast h₀
    if hxy : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ≠ 0 then
      exact HalfSq.le.AddAddHalfSqInner_MulSub1HalfSqSub.of.All_Ne_0.Gt_2 h₀ hxy
    else
      obtain ⟨t₀, -, hx₀⟩ : ∃ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) = 0 := by
        push Not at hxy
        exact hxy
      if hx : x = 0 then
        subst hx
        have hg : half_sq' (0 : LpSpace p d) = 0 := by
          ext i
          simp [half_sq']
        simp only [hg, half_sq, toL2, sub_zero, norm_zero]
        simp
        nlinarith [sq_nonneg ‖y‖]
      else
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := not_forall.1 fun hc => hx (by ext i; exact hc i)
        if hd : ∃ j, j ≠ i then
          obtain ⟨j, hj⟩ := hd
          let u : LpSpace p d := WithLp.toLp p (Pi.single j 1)
          let yk : ℕ → LpSpace p d := fun k => y + (1 / ((k : ℝ) + 1)) • u
          have hk : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (yk k - x) ≠ 0 := fun k t _ he => by
            have ei := congrArg (fun z : LpSpace p d => z i) he
            have ej := congrArg (fun z : LpSpace p d => z j) he
            have e0 := congrArg (fun z : LpSpace p d => z i) hx₀
            have e0j := congrArg (fun z : LpSpace p d => z j) hx₀
            simp [yk, u, Ne.symm hj] at ei ej e0 e0j
            have hyx : y i - x i ≠ 0 := fun h0 => hi (by rw [h0, mul_zero, add_zero] at e0; exact e0)
            have htt : t = t₀ :=
              sub_eq_zero.1 ((mul_eq_zero.1 (by linear_combination ei - e0 : (t - t₀) * (y i - x i) = 0)).resolve_right hyx)
            rw [← htt] at e0j
            have ht0 : t = 0 :=
              (mul_eq_zero.1 (by linear_combination ej - e0j : t * ((k : ℝ) + 1)⁻¹ = 0)).resolve_right (by positivity)
            rw [ht0, zero_mul, add_zero] at ei
            exact hi ei
          have hlim : Tendsto yk atTop (𝓝 y) := by
            have := (tendsto_const_nhds (x := y)).add (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const u : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • u) atTop (𝓝 ((0 : ℝ) • u)))
            simpa [yk] using this
          have hL : Continuous fun z : LpSpace p d => half_sq z := ContinuousHalfSq.of.Ge_1 (by omega)
          have hT : Continuous fun z : LpSpace p d => z.toL2 := by
            unfold toL2
            fun_prop
          have hR : Continuous fun z : LpSpace p d => half_sq x + inner ℝ (half_sq' x).toL2 (z - x).toL2 + (p - 1) * half_sq (z - x) :=
            (continuous_const.add (continuous_const.inner (hT.comp (continuous_id.sub continuous_const)))).add
              (continuous_const.mul (hL.comp (continuous_id.sub continuous_const)))
          exact le_of_tendsto_of_tendsto' ((hL.tendsto y).comp hlim) ((hR.tendsto y).comp hlim)
            fun k => HalfSq.le.AddAddHalfSqInner_MulSub1HalfSqSub.of.All_Ne_0.Gt_2 h₀ (hk k)
        else
          have hd' : ∀ j, j = i := fun j => not_not.1 fun hj => hd ⟨j, hj⟩
          have hs : ∀ f : Fin d → ℝ, ∑ j, f j = f i := fun f => Fintype.sum_eq_single i fun j hj => absurd (hd' j) hj
          have hn : ∀ z : LpSpace p d, ‖z‖ = |z i| := fun z => by
            have e := PowNorm.eq.Sum_PowAbs.of.Ge_1 (x := z) (by omega)
            rw [hs] at e
            exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) (by omega)).1 e
          have hin : inner ℝ (half_sq' x).toL2 (y - x).toL2 = (y i - x i) * x i := by
            simp only [toL2, half_sq', PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial, WithLp.ofLp_sub, Pi.sub_apply]
            rw [hs, hn x, ← Real.rpow_add (abs_pos.2 hi), show 2 - (p : ℝ) + (p - 2) = 0 by ring, Real.rpow_zero, one_mul]
          simp only [half_sq]
          rw [hin, hn y, hn x, hn (y - x)]
          simp only [sq_abs, WithLp.ofLp_sub, Pi.sub_apply]
          have hp1 : (1 : ℝ) ≤ p - 1 := by linarith
          nlinarith [sq_nonneg (y i - x i), mul_le_mul_of_nonneg_right hp1 (sq_nonneg (y i - x i))]


-- created on 2026-09-26