import Mathlib
import sympy.Basic
import sympy.Analysis.Asymptotics.BenderProductCoefficient

open Filter

/--
[bender_product_coefficient_asymptotic_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/BenderProductCoefficient.lean)
-/
@[path]
private lemma bender_product_coefficient_asymptotic_general_eq
-- given
  (a b : ℕ → ℝ) (α : ENNReal) (β : NNReal)
  (hA : (FormalMultilinearSeries.ofScalars ℝ a).radius = α)
  (hαβ : ENNReal.ofNNReal β < α)
  (hbnz : ∀ᶠ n in atTop, b n ≠ 0)
  (hratio : Tendsto (fun n => b (n - 1) / b n) atTop (nhds (β : ℝ)))
  (hAβ : FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) ≠ 0) :
-- imply
  Asymptotics.IsEquivalent atTop
    (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b))
    (fun n => FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) * b n) :=
-- proof
  Real.Asymptotics.BenderProductCoefficient.bender_product_coefficient_asymptotic_general
    a b α β hA hαβ hbnz hratio hAβ


/--
[bender_product_coefficient_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/BenderProductCoefficient.lean)
-/
@[path]
private lemma bender_product_coefficient_asymptotic_eq
-- given
  (a b : ℕ → ℝ) (α : ENNReal) (β : NNReal)
  (hA : (FormalMultilinearSeries.ofScalars ℝ a).radius = α)
  (hB : (FormalMultilinearSeries.ofScalars ℝ b).radius = ENNReal.ofNNReal β)
  (hαβ : ENNReal.ofNNReal β < α)
  (hbnz : ∀ᶠ n in atTop, b n ≠ 0)
  (hratio : Tendsto (fun n => b (n - 1) / b n) atTop (nhds (β : ℝ)))
  (hAβ : FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) ≠ 0) :
-- imply
  Asymptotics.IsEquivalent atTop
    (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b))
    (fun n => FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) * b n) :=
-- proof
  Real.Asymptotics.BenderProductCoefficient.bender_product_coefficient_asymptotic
    a b α β hA hB hαβ hbnz hratio hAβ


-- created on 2026-10-09
