import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.WeierstrassPreparation

open Complex.WeierstrassPreparationWanted

/-- [weierstrass_preparation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/WeierstrassPreparation.lean) -/
@[path]
private lemma weierstrass_preparation_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {f : E × ℂ → ℂ} {d : ℕ} {g : ℂ → ℂ}
  (hf : AnalyticAt ℂ f (0 : E × ℂ))
  (hg : AnalyticAt ℂ g (0 : ℂ))
  (hg0 : g (0 : ℂ) ≠ 0)
  (h_order : ∀ᶠ w in nhds (0 : ℂ), f ((0 : E), w) = w ^ d * g w) :
-- imply
  ∃ (a : Fin d → E → ℂ) (u : E × ℂ → ℂ),
    (∀ j, AnalyticAt ℂ (a j) (0 : E)) ∧
    (∀ j, a j (0 : E) = 0) ∧
    AnalyticAt ℂ u (0 : E × ℂ) ∧ u (0 : E × ℂ) ≠ 0 ∧
    ∃ U : Set (E × ℂ), IsOpen U ∧ (0 : E × ℂ) ∈ U ∧
      ∀ p ∈ U, f p = u p * (p.2 ^ d + ∑ j : Fin d, a j p.1 * p.2 ^ (j : ℕ)) := by
-- proof
  apply weierstrass_preparation hf hg hg0 h_order

-- created on 2026-10-10
