import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.FunctionalEquation
open Complex hiding exp continuous_exp Real Filter Topology Asymptotics FunctionalEquation
open Real Filter Topology Asymptotics


namespace FunctionalEquation

/--
[jacobiTheta_modular_S_transform](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma jacobiTheta_modular_S_transform
  {τ : UpperHalfPlane} :
-- imply
  jacobiTheta ↑(ModularGroup.S • τ) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * jacobiTheta (τ : ℂ) :=
-- proof
  jacobiTheta_S_smul τ

end FunctionalEquation

namespace FunctionalEquation

/--
[gamma_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma gamma_ne_zero
  {s : ℂ}
-- given
  (hs : ∀ m : ℕ, s ≠ -↑m) :
-- imply
  Gamma s ≠ 0 :=
-- proof
  Complex.Gamma_ne_zero hs

end FunctionalEquation

namespace FunctionalEquation

/--
[xi_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma xi_differentiable
-- imply
  Differentiable ℂ xi := by
-- proof
  apply Differentiable.add
  · apply Differentiable.mul
    · exact (differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).div_const 2
    · exact differentiable_completedZeta₀
  · exact differentiable_const _

end FunctionalEquation

namespace FunctionalEquation

/--
[xi_eq_mul_completedZeta](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma xi_eq_mul_completedZeta
  {s : ℂ}
-- given
  (hs0 : s ≠ 0)
  (hs1 : s ≠ 1) :
-- imply
  xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
-- proof
  unfold xi
  rw [completedRiemannZeta_eq]
  have : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

end FunctionalEquation

namespace FunctionalEquation

/--
[xi_functional_equation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma xi_functional_equation
  {s : ℂ} :
-- imply
  xi (1 - s) = xi s := by
-- proof
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

end FunctionalEquation

namespace FunctionalEquation

/--
[completedRiemannZeta_ne_zero_of_one_le_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma completedRiemannZeta_ne_zero_of_one_le_re
  {s : ℂ}
-- given
  (hs_re : 1 ≤ s.re)
  (hs0 : s ≠ 0) :
-- imply
  completedRiemannZeta s ≠ 0 := by
-- proof
  intro h
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs_re
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div] at hζ
  exact hζ rfl

end FunctionalEquation

namespace FunctionalEquation

/--
[completedRiemannZeta_zero_re_in_critical_strip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma completedRiemannZeta_zero_re_in_critical_strip
  {s : ℂ}
-- given
  (hs : completedRiemannZeta s = 0)
  (hs0 : s ≠ 0)
  (hs1 : s ≠ 1) :
-- imply
  0 < s.re ∧ s.re < 1 := by
-- proof
  constructor
  ·
    by_contra h
    push Not at h
    have h1s_re : 1 ≤ (1 - s).re := by simp [sub_re, one_re]; linarith
    have h1s_ne0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have hΛ : completedRiemannZeta (1 - s) = 0 := by
      rw [completedRiemannZeta_one_sub]; exact hs
    exact completedRiemannZeta_ne_zero_of_one_le_re h1s_re h1s_ne0 hΛ
  ·
    by_contra h
    push Not at h
    exact completedRiemannZeta_ne_zero_of_one_le_re h hs0 hs

end FunctionalEquation

namespace FunctionalEquation

/--
[xi_zero_re_in_critical_strip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma xi_zero_re_in_critical_strip
  {s : ℂ}
-- given
  (hs : xi s = 0) :
-- imply
  0 < s.re ∧ s.re < 1 := by
-- proof
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; unfold xi at hs; simp at hs
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; unfold xi at hs; simp at hs
  rw [xi_eq_mul_completedZeta hs0 hs1] at hs
  have hfac : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero
  have hΛ : completedRiemannZeta s = 0 := by
    obtain h | h := mul_eq_zero.mp hs
    · exact absurd h hfac
    · exact h
  exact completedRiemannZeta_zero_re_in_critical_strip s hΛ hs0 hs1

end FunctionalEquation

namespace FunctionalEquation

/--
[xi_entire_functional_equation_and_critical_strip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean)
-/
@[path]
lemma xi_entire_functional_equation_and_critical_strip
-- imply
  (Differentiable ℂ xi) ∧ (∀ s : ℂ, xi (1 - s) = xi s) ∧ (∀ s : ℂ, xi s = 0 → 0 < s.re ∧ s.re < 1) :=
-- proof
  ⟨xi_differentiable, xi_functional_equation, xi_zero_re_in_critical_strip⟩

end FunctionalEquation


-- created on 2026-10-23
