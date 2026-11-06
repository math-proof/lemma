import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Hyperreal.Ne_0.of.InfinitesimalPos
import Lemma.Hyperreal.XEqCos_1.of.Infinitesimal
open Filter Hyperreal


@[path]
private lemma main
  {θ : ℝ*}
-- given
  (h : θ → 0⁺) :
-- imply
  θ.sin / θ.tan ≈ 1 := by
-- proof
  have h_tan : θ.tan ≠ 0 := by
    intro htan
    apply Ne_0.of.InfinitesimalPos h
    have habs := (All_LtAbs.of.Infinitesimal h.2) ⟨π / 2, half_pos Real.pi_pos⟩
    have hzero : (|θ| < ↑(π / 2) ∧ θ.tan = 0) → θ = 0 := by
      apply UFn.of.All_UFn θ
      intro f hf
      obtain ⟨habs, htan⟩ := hf
      let x : ℝ* := Hyperreal.ofSeq f
      have habs' : |x| < ↑(π / 2) := habs
      have htan' : x.tan = 0 := htan
      simp only [abs_lt] at habs'
      dsimp only [Hyperreal.tan] at htan'
      apply Germ.coe_eq.mpr
      have hlt : ∀ᶠ n in hyperfilter ℕ, f n < π / 2 := Germ.coe_lt.mp habs'.2
      have hgt : ∀ᶠ n in hyperfilter ℕ, -(π / 2 : ℝ) < f n := Germ.coe_lt.mp habs'.1
      have htz : ∀ᶠ n in hyperfilter ℕ, Real.tan (f n) = 0 :=
        Germ.coe_eq.mp <| by
          simp only [x, Hyperreal.ofSeq, Germ.map_coe] at htan'
          apply htan'
      filter_upwards [hlt, hgt, htz] with n hn hp ht
      have hmem : f n ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨hp, hn⟩
      apply (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hp, Real.pi_pos]) (by linarith [hn, Real.pi_pos])).mp
      rw [Real.tan_eq_sin_div_cos] at ht
      apply (div_eq_zero_iff.mp ht).resolve_right (Real.cos_pos_of_mem_Ioo hmem).ne'
    simpa using hzero ⟨habs, htan⟩
  have h_eq : θ.sin / θ.tan = θ.cos := by
    revert h_tan
    apply UFn.of.All_UFn θ
    intro f hf
    dsimp only [Hyperreal.sin, Hyperreal.tan, Hyperreal.cos] at hf ⊢
    apply Germ.coe_eq.mpr
    have hne : ∀ᶠ n in hyperfilter ℕ, Real.tan (f n) ≠ 0 := by
      rw [Ultrafilter.eventually_not]
      intro hall
      apply hf
      apply Germ.coe_eq.mpr hall
    filter_upwards [hne] with n hn
    change Real.sin (f n) / Real.tan (f n) = Real.cos (f n)
    have hsin : Real.sin (f n) ≠ 0 := by
      intro hs
      apply hn
      rw [Real.tan_eq_sin_div_cos, hs, zero_div]
    rw [Real.tan_eq_sin_div_cos, div_eq_mul_inv, inv_div, ← mul_div_assoc]
    apply mul_div_cancel_left₀ _ hsin
  rw [h_eq]
  apply XEqCos_1.of.Infinitesimal h.2


-- created on 2026-11-05
