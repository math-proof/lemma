import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

noncomputable section

namespace EisensteinGeneral.LocalCorrection

def geomSum (χϖ : ℂ) (N : ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (M + 1), (χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k

def ramSum (N : ℕ) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) : ℂ :=
  c₀ + ∑ k ∈ Finset.Icc 1 K, (((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k

def corrOff (χϖ : ℂ) (N : ℕ) (e : ℤ) (s : ℂ) : ℂ :=
  if e ≤ 0 then geomSum χϖ N (-e).toNat s else 0

def corrOn (N : ℕ) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) : ℂ :=
  if e ≤ n + (max m c : ℕ) then
    (μ𝒪 : ℂ)⁻¹ * ramSum N (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat c₀ sh s
  else 0

theorem geomSum_def (χϖ : ℂ) (N M : ℕ) (s : ℂ) :
    geomSum χϖ N M s = ∑ k ∈ Finset.range (M + 1), (χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k := rfl

theorem ramSum_def (N K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) :
    ramSum N K c₀ sh s = c₀ + ∑ k ∈ Finset.Icc 1 K, (((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k := rfl

theorem corrOff_def (χϖ : ℂ) (N : ℕ) (e : ℤ) (s : ℂ) :
    corrOff χϖ N e s = if e ≤ 0 then geomSum χϖ N (-e).toNat s else 0 := rfl

theorem corrOn_def (N : ℕ) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) :
    corrOn N n c m e μ𝒪 c₀ sh s =
      if e ≤ n + (max m c : ℕ) then (μ𝒪 : ℂ)⁻¹ * ramSum N (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat c₀ sh s
      else 0 := rfl

theorem differentiable_cpow_neg_two_mul {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s))) :=
  Differentiable.const_cpow (differentiable_id.const_mul (2 : ℂ)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

theorem differentiable_cpow_neg_two_mul_add_one {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s + 1))) :=
  Differentiable.const_cpow ((differentiable_id.const_mul (2 : ℂ)).add (differentiable_const 1)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

theorem geomSum_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    Differentiable ℂ (geomSum χϖ N M) := by
  unfold geomSum
  exact Differentiable.fun_sum fun k _ => ((differentiable_cpow_neg_two_mul hN).const_mul χϖ).pow k

theorem ramSum_differentiable {N : ℕ} (hN : 0 < N) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) :
    Differentiable ℂ (ramSum N K c₀ sh) := by
  unfold ramSum
  exact (differentiable_const c₀).add
    (Differentiable.fun_sum fun k _ => ((differentiable_cpow_neg_two_mul_add_one hN).pow k).mul_const (sh k))

theorem corrOff_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (e : ℤ) :
    Differentiable ℂ (corrOff χϖ N e) := by
  unfold corrOff
  by_cases he : e ≤ 0
  · simp only [he, ↓reduceIte]
    exact geomSum_differentiable χϖ hN _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

theorem corrOn_differentiable {N : ℕ} (hN : 0 < N) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ)
    (sh : ℕ → ℂ) : Differentiable ℂ (corrOn N n c m e μ𝒪 c₀ sh) := by
  unfold corrOn
  by_cases he : e ≤ n + (max m c : ℕ)
  · simp only [he, ↓reduceIte]
    exact (ramSum_differentiable hN _ c₀ sh).const_mul _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

end EisensteinGeneral.LocalCorrection

end
