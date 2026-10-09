import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.PowPowAddDivNeg1'2DivMulISqrt3'2'3.eq.One
import Lemma.Complex.PowAddDivNeg1'2DivMulISqrt3'2.eq.PowAddDivNeg1'2DivMulISqrt3'2EMod3
import Lemma.Complex.SquarePow_Div1'2.eq.Self
import Lemma.Complex.AddPowPowPowPow.eq.Neg
import Lemma.Complex.MulMulPowPowPow.eq.DivNeg3.of.EqSubCeil.Eq_AddDivMul4Pow3'27Square


@[path]
private lemma sub
  {x α β γ p q δ' δ y y₀ y₁ : ℂ}
  {d : ℤ}
-- given
  (hp : p = -γ - (-α / 2) ^ 2 / 3)
  (hq : q = (-α / 2) ^ 3 / 27 * 2 + (-β ^ 2 / 8 + α * γ / 2) - (-α / 2) * (-γ) / 3)
  (hδ' : δ' = 4 * p ^ 3 / 27 + q ^ 2)
  (h₀ : ⌈3 * arg (-p / 3) / (π * 2) - 1 / 2⌉ - (if p * (⌈(arg (δ' ^ (1 / 2 : ℂ) - q) + arg (-δ' ^ (1 / 2 : ℂ) - q)) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then 0 else if arg (δ' ^ (1 / 2 : ℂ) - q) + arg (-δ' ^ (1 / 2 : ℂ) - q) > π then 1 else -1) = d)
  (hδ : δ = -(α ^ 2 / 3 + 4 * γ) ^ 3 / 27 + (-α ^ 3 / 27 + 4 * α * γ / 3 - β ^ 2 / 2) ^ 2)
  (hy : y = (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ) * (-1 / 2 + Complex.I * √3 / 2) ^ d + (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ))
  (hy₀ : y₀ = -2 * α / 3 + y)
  (hy₁ : y₁ = 4 * α / 3 + y)
  (h : x ^ 4 + α * x ^ 2 + β * x + γ = 0)
  (hβ : β ≠ 0) :
-- imply
  x = (2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 - y₀ ^ (1 / 2 : ℂ) / 2 ∨
  x = -(2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 - y₀ ^ (1 / 2 : ℂ) / 2 ∨
  x = (-2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 + y₀ ^ (1 / 2 : ℂ) / 2 ∨
  x = -(-2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 + y₀ ^ (1 / 2 : ℂ) / 2 := by
-- proof
  have scale : ∀ (c : ℝ) (z e : ℂ), 0 < c → ((c : ℂ) * z) ^ e = (c : ℂ) ^ e * z ^ e := by
    intro c z e hc
    by_cases hz : z = 0
    · subst hz
      by_cases he : e = 0
      · subst he
        simp
      · simp [Complex.zero_cpow he]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hc' hz), Complex.cpow_def_of_ne_zero hc', Complex.cpow_def_of_ne_zero hz, ← Complex.exp_add, Complex.log_ofReal_mul hc hz, Complex.ofReal_log hc.le]
    ring_nf
  have c16 : ((16 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 4 := by
    rw [show ((16 : ℝ) : ℂ) = (4 : ℂ) ^ 2 by norm_num, one_div]
    exact_mod_cast Complex.pow_cpow_nat_inv (x := 4) (n := 2) (by norm_num) (by simp; positivity) (by simp; positivity)
  have c8 : ((8 : ℝ) : ℂ) ^ (1 / 3 : ℂ) = 2 := by
    rw [show ((8 : ℝ) : ℂ) = (2 : ℂ) ^ 3 by norm_num, one_div]
    exact_mod_cast Complex.pow_cpow_nat_inv (x := 2) (n := 3) (by norm_num) (by simp; positivity) (by simp; positivity)
  have hs' : δ ^ (1 / 2 : ℂ) = 4 * δ' ^ (1 / 2 : ℂ) := by
    have e : δ = ((16 : ℝ) : ℂ) * δ' := by rw [hδ, hδ', hp, hq]; push_cast; ring
    rw [e, scale 16 δ' _ (by norm_num), c16]
  have hA : (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ) = 2 * (δ' ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) := by
    have e : α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + δ ^ (1 / 2 : ℂ) = ((8 : ℝ) : ℂ) * (δ' ^ (1 / 2 : ℂ) / 2 - q / 2) := by
      rw [hs', hq]; push_cast; ring
    rw [e, scale 8 _ _ (by norm_num), c8]
  have hB : (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ) = 2 * (-δ' ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) := by
    have e : α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - δ ^ (1 / 2 : ℂ) = ((8 : ℝ) : ℂ) * (-δ' ^ (1 / 2 : ℂ) / 2 - q / 2) := by
      rw [hs', hq]; push_cast; ring
    rw [e, scale 8 _ _ (by norm_num), c8]
  have hK := Complex.MulMulPowPowPow.eq.DivNeg3.of.EqSubCeil.Eq_AddDivMul4Pow3'27Square hδ' h₀
  have hW3 := Complex.PowPowAddDivNeg1'2DivMulISqrt3'2'3.eq.One (d := d)
  have hsum := Complex.AddPowPowPowPow.eq.Neg (q := q) (δ := δ')
  rw [hA, hB] at hy
  generalize (δ' ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) = A' at hK hsum hy
  generalize (-δ' ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) = B' at hK hsum hy
  generalize (-1 / 2 + Complex.I * √3 / 2 : ℂ) ^ d = W at hK hW3 hy
  have hres : (y / 2) ^ 3 + p * (y / 2) + q = 0 := by
    rw [hy]
    linear_combination (3 * (A' * W + B')) * hK + A' ^ 3 * hW3 + hsum
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (y + α / 3) / 2 := ⟨_, rfl⟩
  have hβ2 : β ^ 2 = y₀ * (4 * r ^ 2 - 4 * γ) := by
    rw [hy₀, hr]
    rw [hp, hq] at hres
    linear_combination (-8 : ℂ) * hres
  have hy0 : y₀ ≠ 0 := by
    intro h0
    apply hβ
    have : β ^ 2 = 0 := by rw [hβ2, h0]; ring
    exact (pow_eq_zero_iff (by norm_num)).mp this
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = y₀ ^ (1 / 2 : ℂ) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = y₀ := by rw [hs]; exact Complex.SquarePow_Div1'2.eq.Self y₀
  have hsne : s ≠ 0 := by
    intro h0
    apply hy0
    rw [← hs2, h0]
    ring
  rw [← hs]
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = β / s := ⟨_, rfl⟩
  have hb : β = u * s := by rw [hu]; field_simp
  have e1 : 2 * β / s = 2 * u := by rw [hu]; ring
  have e2 : -2 * β / s = -2 * u := by rw [hu]; ring
  rw [e1, e2]
  obtain ⟨t0, ht0d⟩ : ∃ t : ℂ, t = (2 * u - y₁) ^ (1 / 2 : ℂ) := ⟨_, rfl⟩
  obtain ⟨t1, ht1d⟩ : ∃ t : ℂ, t = (-2 * u - y₁) ^ (1 / 2 : ℂ) := ⟨_, rfl⟩
  rw [← ht0d, ← ht1d]
  have ha : α = 2 * r - s ^ 2 := by rw [hs2, hy₀, hr]; ring
  have hy1 : y₁ = 4 * r - s ^ 2 := by rw [hs2, hy₁, hy₀, hr]; ring
  have ht0 : t0 ^ 2 = 2 * u - 4 * r + s ^ 2 := by rw [ht0d, Complex.SquarePow_Div1'2.eq.Self, hy1]; ring
  have ht1 : t1 ^ 2 = -2 * u - 4 * r + s ^ 2 := by rw [ht1d, Complex.SquarePow_Div1'2.eq.Self, hy1]; ring
  have hg : γ = r ^ 2 - u ^ 2 / 4 := by
    have e : y₀ * (u ^ 2 - (4 * r ^ 2 - 4 * γ)) = 0 := by
      linear_combination hβ2 - (β + u * s) * hb - u ^ 2 * hs2
    rcases mul_eq_zero.mp e with h0 | h0
    · exact absurd h0 hy0
    · linear_combination h0 / 4
  have fac : (x - (t0 / 2 - s / 2)) * (x - (-t0 / 2 - s / 2)) * ((x - (t1 / 2 + s / 2)) * (x - (-t1 / 2 + s / 2))) = 0 := by
    rw [← h]
    linear_combination (-x ^ 2) * ha + (-x) * hb + (-1 : ℂ) * hg + (-(-s - t1 + 2 * x) * (-s + t1 + 2 * x) / 16) * ht0 + (-(2 * r + 2 * s * x - u + 2 * x ^ 2) / 8) * ht1
  rcases mul_eq_zero.mp fac with h12 | h34
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · left; linear_combination h1
    · right; left; linear_combination h2
  · rcases mul_eq_zero.mp h34 with h3 | h4
    · right; right; left; linear_combination h3
    · right; right; right; linear_combination h4


@[path]
private lemma mod_3
  {x α β γ p q δ' δ y y₀ y₁ : ℂ}
  {d : ℤ}
-- given
  (hp : p = -γ - (-α / 2) ^ 2 / 3)
  (hq : q = (-α / 2) ^ 3 / 27 * 2 + (-β ^ 2 / 8 + α * γ / 2) - (-α / 2) * (-γ) / 3)
  (hδ' : δ' = 4 * p ^ 3 / 27 + q ^ 2)
  (h₀ : (⌈3 * arg (-p / 3) / (π * 2) - 1 / 2⌉ - (if p * (⌈(arg (δ' ^ (1 / 2 : ℂ) - q) + arg (-δ' ^ (1 / 2 : ℂ) - q)) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then 0 else if arg (δ' ^ (1 / 2 : ℂ) - q) + arg (-δ' ^ (1 / 2 : ℂ) - q) > π then 1 else -1)) % 3 = d)
  (hδ : δ = -(α ^ 2 / 3 + 4 * γ) ^ 3 / 27 + (-α ^ 3 / 27 + 4 * α * γ / 3 - β ^ 2 / 2) ^ 2)
  (hy : y = (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ) * (-1 / 2 + Complex.I * √3 / 2) ^ d + (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ))
  (hy₀ : y₀ = -2 * α / 3 + y)
  (hy₁ : y₁ = 4 * α / 3 + y)
  (h : x ^ 4 + α * x ^ 2 + β * x + γ = 0)
  (hβ : β ≠ 0) :
-- imply
  x = (2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 - y₀ ^ (1 / 2 : ℂ) / 2 ∨
  x = -(2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 - y₀ ^ (1 / 2 : ℂ) / 2 ∨
  x = (-2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 + y₀ ^ (1 / 2 : ℂ) / 2 ∨
  x = -(-2 * β / y₀ ^ (1 / 2 : ℂ) - y₁) ^ (1 / 2 : ℂ) / 2 + y₀ ^ (1 / 2 : ℂ) / 2 := by
-- proof
  obtain ⟨D, hD⟩ : ∃ D : ℤ, ⌈3 * arg (-p / 3) / (π * 2) - 1 / 2⌉ - (if p * (⌈(arg (δ' ^ (1 / 2 : ℂ) - q) + arg (-δ' ^ (1 / 2 : ℂ) - q)) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then 0 else if arg (δ' ^ (1 / 2 : ℂ) - q) + arg (-δ' ^ (1 / 2 : ℂ) - q) > π then 1 else -1) = D := ⟨_, rfl⟩
  rw [hD] at h₀
  have hy' : y = (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ) * (-1 / 2 + Complex.I * √3 / 2) ^ D + (α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - δ ^ (1 / 2 : ℂ)) ^ (1 / 3 : ℂ) := by
    rw [hy, ← h₀, ← Complex.PowAddDivNeg1'2DivMulISqrt3'2.eq.PowAddDivNeg1'2DivMulISqrt3'2EMod3]
  exact sub hp hq hδ' hD hδ hy' hy₀ hy₁ h hβ


-- created on 2018-11-27
