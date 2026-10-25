import Mathlib
import sympy.Basic
import Def.Analysis.Complex.Wiman.TwoPowerBadSets
open Filter MeasureTheory Set
open scoped ENNReal
open Complex


namespace Complex

/--
[exists_finite_wimanExceptionalSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/TwoPowerBadSets.lean)
-/
@[path]
lemma exists_finite_wimanExceptionalSet
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∃ x₀ : ℝ,
    volume (wimanExceptionalSet f x₀) < ∞ ∧
    ∀ x, x₀ ≤ x → x ∉ wimanExceptionalSet f x₀ →
    iteratedDeriv 2 (wimanGrowth f) x ≤
    wimanGrowth f x ^ (81 / 64 : ℝ) := by
-- proof
  obtain ⟨a, hgpos_a, hgmono_a, hdmono_a, hC2, hd_atTop⟩ :=
    eventually_wimanGrowth_regular f hf htrans
  have hd_eventually_pos : ∀ᶠ x : ℝ in atTop, 0 < deriv (wimanGrowth f) x :=
    hd_atTop.eventually (eventually_gt_atTop 0)
  obtain ⟨b, hdb⟩ := eventually_atTop.1 hd_eventually_pos
  let x₀ : ℝ := max a b
  have hax₀ : a ≤ x₀ := le_max_left _ _
  have hbx₀ : b ≤ x₀ := le_max_right _ _
  have hgpos : ∀ x, x₀ ≤ x → 0 < wimanGrowth f x := by
    intro x hx
    exact hgpos_a x (hax₀.trans hx)
  have hdpos : ∀ x, x₀ ≤ x → 0 < deriv (wimanGrowth f) x := by
    intro x hx
    exact hdb x (hbx₀.trans hx)
  have hgmono : MonotoneOn (wimanGrowth f) (Ici x₀) :=
    hgmono_a.mono fun _ hx => hax₀.trans hx
  have hdmono : MonotoneOn (deriv (wimanGrowth f)) (Ici x₀) :=
    hdmono_a.mono fun _ hx => hax₀.trans hx
  have hgC1 : ContDiff ℝ 1 (wimanGrowth f) := hC2.of_le (by norm_num)
  have hdC1 : ContDiff ℝ 1 (deriv (wimanGrowth f)) := by
    exact hC2.deriv'
  have hfirstFinite :
    volume (Real.powerGrowthBadSet (wimanGrowth f) (9 / 8 : ℝ) x₀) < ∞ :=
    Real.volume_powerGrowthBadSet_lt_top (wimanGrowth f) (by norm_num) hgpos hgmono hgC1
  have hsecondFinite :
    volume (Real.powerGrowthBadSet (deriv (wimanGrowth f)) (9 / 8 : ℝ) x₀) < ∞ :=
    Real.volume_powerGrowthBadSet_lt_top (deriv (wimanGrowth f)) (by norm_num)
      hdpos hdmono hdC1
  have hfinite : volume (wimanExceptionalSet f x₀) < ∞ := by
    rw [wimanExceptionalSet]
    exact measure_union_lt_top hfirstFinite hsecondFinite
  refine ⟨x₀, hfinite, ?_⟩
  intro x hx hxgood
  have hxfirst :
    x ∉ Real.powerGrowthBadSet (wimanGrowth f) (9 / 8 : ℝ) x₀ := by
    intro hbad
    exact hxgood (by exact Or.inl hbad)
  have hxsecond :
    x ∉ Real.powerGrowthBadSet (deriv (wimanGrowth f)) (9 / 8 : ℝ) x₀ := by
    intro hbad
    exact hxgood (by exact Or.inr hbad)
  have hfirst :
    deriv (wimanGrowth f) x < wimanGrowth f x ^ (9 / 8 : ℝ) := by
    simpa only [Real.powerGrowthBadSet, mem_ofPred_eq, hx, true_and, not_le] using hxfirst
  have hsecond :
    deriv (deriv (wimanGrowth f)) x <
      deriv (wimanGrowth f) x ^ (9 / 8 : ℝ) := by
    simpa only [Real.powerGrowthBadSet, mem_ofPred_eq, hx, true_and, not_le] using hxsecond
  have hsecondDeriv :
    deriv (deriv (wimanGrowth f)) = iteratedDeriv 2 (wimanGrowth f) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hsecondDeriv] at hsecond
  have hgx : 0 < wimanGrowth f x := hgpos x hx
  have hdx : 0 < deriv (wimanGrowth f) x := hdpos x hx
  calc
    iteratedDeriv 2 (wimanGrowth f) x ≤
      deriv (wimanGrowth f) x ^ (9 / 8 : ℝ) := hsecond.le
    _ ≤ (wimanGrowth f x ^ (9 / 8 : ℝ)) ^ (9 / 8 : ℝ) :=
      Real.rpow_le_rpow hdx.le hfirst.le (by norm_num)
    _ = wimanGrowth f x ^ ((9 / 8 : ℝ) * (9 / 8 : ℝ)) :=
      (Real.rpow_mul hgx.le (9 / 8 : ℝ) (9 / 8 : ℝ)).symm
    _ = wimanGrowth f x ^ (81 / 64 : ℝ) := by norm_num
end



-- created on 2026-10-20
-- updated on 2026-10-23
