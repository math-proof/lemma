import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.Continuity
open Filter StatMech StatMech.RSW StatMech.RSW.Continuity


/--
[roc_eq_zero_of_le_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Continuity.lean)
-/
@[path]
private lemma roc_eq_zero_of_le_tendsto_eq
  {a : ℕ → ℝ}
  {θ : ℝ}
-- given
  (hθ0 : 0 ≤ θ)
  (hle : ∀ n, θ ≤ a n)
  (hlim : Tendsto a atTop (nhds 0)) :
-- imply
  θ = 0 := by
-- proof
  apply StatMech.RSW.Continuity.roc_eq_zero_of_le_tendsto hθ0 hle hlim

/--
[roc_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Continuity.lean)
-/
@[path]
private lemma roc_continuity_eq
  {a : ℕ → ℝ}
  {θ c : ℝ}
-- given
  (hc0 : 0 < c)
  (hc1 : c < 1)
  (hθ0 : 0 ≤ θ)
  (hθle : ∀ n, θ ≤ a n)
  (hnn : ∀ n, 0 ≤ a n)
  (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
-- imply
  θ = 0 := by
-- proof
  apply StatMech.RSW.Continuity.roc_continuity a hc0 hc1 hθ0 hθle hnn hann

/--
[roc_continuity_of_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Continuity.lean)
-/
@[path]
private lemma roc_continuity_of_polynomial_eq
  {a : ℕ → ℝ}
  {θ ε C : ℝ}
-- given
  (hε : 0 < ε)
  (hθ0 : 0 ≤ θ)
  (hθle : ∀ n, θ ≤ a n)
  (hpoly : ∀ n, 1 ≤ n → a n ≤ C * (n : ℝ) ^ (-ε)) :
-- imply
  θ = 0 := by
-- proof
  apply StatMech.RSW.Continuity.roc_continuity_of_polynomial a hε hθ0 hθle hpoly


-- created on 2026-10-23
