import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWAspectInduction
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[rai_cross_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAspectInduction.lean)
-/
@[path]
private lemma rai_cross_def_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {k : ℕ} :
-- imply
  rai_cross μ n k = μ.real (horizontalCrossingEvent 0 ((k : ℤ) * n) 0 n) := by
-- proof
  apply StatMech.Universality.rai_cross_def μ n k

/--
[rai_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAspectInduction.lean)
-/
@[path]
private lemma rai_step_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {k : ℕ}
  {cL γ : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 < n)
  (hk : 1 ≤ k)
  (hcL0 : 0 ≤ cL)
  (hγ0 : 0 ≤ γ)
  (hL : cL ≤ rai_cross μ n k)
  (h2box : γ ≤ μ.real (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n))
  (hband : (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n)) :
-- imply
  cL * (1 / 2) * γ ≤ rai_cross μ n (k + 1) := by
-- proof
  apply StatMech.Universality.rai_step μ hpa hn hk hcL0 hγ0 hL h2box hband

/--
[rai_cross_lb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAspectInduction.lean)
-/
@[path]
private lemma rai_cross_lb_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 < n)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hseed : β ≤ rai_cross μ n 1)
  (h2box : ∀ k : ℕ, 1 ≤ k → γ ≤ μ.real (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n))
  (hband : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n)) :
-- imply
  ∀ k : ℕ, 1 ≤ k → β * ((1 / 2) * γ) ^ (k - 1) ≤ rai_cross μ n k := by
-- proof
  apply StatMech.Universality.rai_cross_lb μ hpa hn hβ hγ hseed h2box hband

/--
[rai_cross_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAspectInduction.lean)
-/
@[path]
private lemma rai_cross_pos_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 < n)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hseed : β ≤ rai_cross μ n 1)
  (h2box : ∀ k : ℕ, 1 ≤ k → γ ≤ μ.real (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n))
  (hband : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n)) :
-- imply
  ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ c ≤ rai_cross μ n k := by
-- proof
  apply StatMech.Universality.rai_cross_pos μ hpa hn hβ hγ hseed h2box hband


-- created on 2026-10-23
