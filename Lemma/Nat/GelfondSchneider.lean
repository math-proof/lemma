import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GelfondSchneider
open scoped Topology ENNReal
open Filter
open scoped NumberField
open MathlibExt.NumberTheory.TranscendenceWanted


/--
[gelfondSchneider_complex_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GelfondSchneider.lean)
-/
@[path]
private lemma gelfondSchneider_complex_exp_eq
  :
-- imply
  ∀ {a b z : ℂ}, IsAlgebraic ℚ a → IsAlgebraic ℚ b → a ≠ 1 →
    b ∉ Set.range (algebraMap ℚ ℂ) → Complex.exp z = a →
    Transcendental ℚ (Complex.exp (b * z)) := by
-- proof
  apply MathlibExt.NumberTheory.TranscendenceWanted.gelfondSchneider_complex_exp

/--
[gelfondSchneider_real_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GelfondSchneider.lean)
-/
@[path]
private lemma gelfondSchneider_real_rpow_eq
  :
-- imply
  ∀ (α β : ℝ), 0 < α → α ≠ 1 → IsAlgebraic ℚ α → IsAlgebraic ℚ β →
    Irrational β → Transcendental ℚ (Real.rpow α β) := by
-- proof
  apply MathlibExt.NumberTheory.TranscendenceWanted.gelfondSchneider_real_rpow


-- created on 2026-10-20
