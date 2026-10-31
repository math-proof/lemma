import Notation.Probability.HasLaw
import Def.Probability.ChiSquare
import Def.Probability.Fisher
import Lemma.Measure.FisherReal.eq.MapProdChiSquaredRealChiSquaredReal
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Measure


/--
Independent chi-squared random variables yield a Fisher–Snedecor law after the
mean-square ratio `(X / d_x) / (Y / d_y)`.

Characterization of `fisherReal` as that pushforward:
[fisherReal = map ((u/d_x)/(v/d_y))](?module=Measure.FisherReal.eq.MapProdChiSquaredRealChiSquaredReal).
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  [NeZero (d_x : ℕ)]
  [NeZero (d_y : ℕ)]
  {X Y : Ω → ℝ}
-- given
  (h₀ : X ⟂ᵢ[π] Y)
  (h₁ : X ∼[π] Real.chiSquare d_x)
  (h₂ : Y ∼[π] Real.chiSquare d_y) :
-- imply
  ((X / (d_x : Ω → ℝ)) / (Y / (d_y : Ω → ℝ))) ∼[π] fisherReal d_x d_y := by
-- proof
  have hprod := h₀.hasLaw_prod h₁ h₂
  let ψ : ℝ × ℝ → ℝ := fun p ↦ (p.1 / (d_x : ℝ)) / (p.2 / (d_y : ℝ))
  have hψ : HasLaw ψ (fisherReal d_x d_y)
    ((Real.chiSquare d_x).prod (Real.chiSquare d_y)) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [ψ] using
      (FisherReal.eq.MapProdChiSquaredRealChiSquaredReal).symm
  have hcomp :
    ((X / (d_x : Ω → ℝ)) / (Y / (d_y : Ω → ℝ))) =
      ψ ∘ fun ω ↦ (X ω, Y ω) := by
    funext ω
    simp [ψ, Pi.div_apply, Pi.natCast_apply]
  rw [hcomp]
  apply hψ.fun_comp hprod


-- created on 2026-10-30
