import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped SchwartzMap


private lemma helper_main (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
  ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) ∧ (∀ x, ‖g x‖ ≤ 1) ∧
    (∀ x, ‖x‖ ≤ 1 → g x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → g x = 0) := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : E → ℂ := fun x => ((b x : ℝ) : ℂ)
  have hfc : HasCompactSupport f := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hfs : ContDiff ℝ (⊤ : ENat) f := (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have happ : ∀ x, hfc.toSchwartzMap hfs x = f x := fun _ => rfl
  refine ⟨hfc.toSchwartzMap hfs, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hco : ((hfc.toSchwartzMap hfs : 𝓢(E, ℂ)) : E → ℂ) = f := funext happ
    rwa [hco]
  ·
    intro x
    rw [happ]
    exact ⟨by simpa [f] using b.nonneg, by simp [f]⟩
  ·
    intro x
    rw [happ]
    simp only [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  ·
    intro x hx
    rw [happ]
    simp only [f, Complex.ofReal_eq_one]
    exact b.one_of_mem_closedBall (by simpa using hx)
  ·
    intro x hx
    rw [happ]
    simp only [f, Complex.ofReal_eq_zero]
    exact b.zero_of_le_dist (by simpa using hx)
/--
[SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
-- imply
  ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → g x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → g x = 0) :=
-- proof
  helper_main E


-- created on 2026-10-23
