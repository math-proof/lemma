import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Data.ENNReal.Real

export Complex (I)
noncomputable abbrev π : ℝ := Real.pi
notation "∞" => Hyperreal.omega


/-!
# Lossy coercion ℝ≥0∞ → ℝ (scoped)

`open scoped ENNReal.ToRealCoe` makes `(x : ℝ)` elaborate to `ENNReal.toReal x` for `x : ℝ≥0∞`
(so that `(ℙ[π](x | y) : ℝ).log` reads like textbook mathematics).
The coercion sends ∞ ↦ 0, so it is deliberately *not* a global instance.
-/
namespace ENNReal.ToRealCoe

noncomputable scoped instance : CoeTC ENNReal ℝ := ⟨ENNReal.toReal⟩

end ENNReal.ToRealCoe
