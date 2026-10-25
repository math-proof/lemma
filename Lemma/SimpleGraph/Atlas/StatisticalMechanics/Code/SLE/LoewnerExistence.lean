import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
open Complex Set Metric Filter Topology StatMech StatMech.SLE


/--
[picard_exists_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma picard_exists_ball_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
  {f : ℝ → E → E}
  {tmin tmax : ℝ}
  {t₀ : Icc tmin tmax}
  {x₀ : E}
  {a L K : ℝ≥0}
-- given
  (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
-- imply
  ∃ α : ℝ → E, α t₀ = x₀ ∧ (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧ (∀ t, α t ∈ closedBall x₀ a) := by
-- proof
  apply StatMech.SLE.picard_exists_ball hf

/--
[picard_exists_ball_family_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma picard_exists_ball_family_lipschitz_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
  {f : ℝ → E → E}
  {tmin tmax : ℝ}
  {t₀ : Icc tmin tmax}
  {x₀ : E}
  {a r L K : ℝ≥0}
-- given
  (hf : IsPicardLindelof f t₀ x₀ a r L K) :
-- imply
  ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧ (∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧ (∀ t, α x t ∈ closedBall x₀ a)) ∧ ∃ C : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith C (fun x ↦ α x t) (closedBall x₀ r) := by
-- proof
  apply StatMech.SLE.picard_exists_ball_family_lipschitz hf

/--
[loewner_local_flow_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma loewner_local_flow_chart_eq
  {W : ℝ → ℝ}
  {z₀ : ℂ}
  {t₀ : ℝ}
-- given
  (hW : Continuous W)
  (hz₀ : 0 < z₀.im) :
-- imply
  ∃ α : ℂ → ℝ → ℂ, (∀ z ∈ closedBall z₀ (z₀.im / 4), α z t₀ = z ∧ (∀ t ∈ Icc (t₀ - z₀.im ^ 2 / 16) (t₀ + z₀.im ^ 2 / 16), HasDerivWithinAt (α z) (loewnerField W t (α z t)) (Icc (t₀ - z₀.im ^ 2 / 16) (t₀ + z₀.im ^ 2 / 16)) t) ∧ (∀ t, α z t ∈ loewnerStrip (z₀.im / 2))) ∧ ∃ C : ℝ≥0, ∀ t ∈ Icc (t₀ - z₀.im ^ 2 / 16) (t₀ + z₀.im ^ 2 / 16), LipschitzOnWith C (fun z ↦ α z t) (closedBall z₀ (z₀.im / 4)) := by
-- proof
  apply StatMech.SLE.loewner_local_flow_chart hW hz₀ t₀

/--
[loewner_local_existence_strip_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma loewner_local_existence_strip_explicit_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  ∃ g : ℝ → ℂ, g 0 = z ∧ (∀ t ∈ Icc (0 : ℝ) (z.im ^ 2 / 8), HasDerivWithinAt g (loewnerField W t (g t)) (Icc (0 : ℝ) (z.im ^ 2 / 8)) t) ∧ (∀ t ∈ Icc (0 : ℝ) (z.im ^ 2 / 8), g t ∈ loewnerStrip (z.im / 2)) := by
-- proof
  apply StatMech.SLE.loewner_local_existence_strip_explicit hW hz

/--
[loewner_local_existence_strip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma loewner_local_existence_strip_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = z ∧ (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt g (loewnerField W t (g t)) (Icc (0 : ℝ) ε) t) ∧ (∀ t ∈ Icc (0 : ℝ) ε, g t ∈ loewnerStrip (z.im / 2)) := by
-- proof
  apply StatMech.SLE.loewner_local_existence_strip hW hz

/--
[loewner_local_existence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma loewner_local_existence_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = z ∧ (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt g (loewnerField W t (g t)) (Icc (0 : ℝ) ε) t) ∧ (∀ t ∈ Icc (0 : ℝ) ε, g t ∈ upperHalfPlane) := by
-- proof
  apply StatMech.SLE.loewner_local_existence hW hz

/--
[loewner_solution_unique_of_strip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma loewner_solution_unique_of_strip_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {ε : ℝ}
  {z : ℂ}
  {g h : ℝ → ℂ}
-- given
  (hδ : 0 < δ)
  (hg0 : g 0 = z)
  (hh0 : h 0 = z)
  (hgc : ContinuousOn g (Icc 0 ε))
  (hgd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
  (hgs : ∀ t ∈ Ico 0 ε, g t ∈ loewnerStrip δ)
  (hhc : ContinuousOn h (Icc 0 ε))
  (hhd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t)
  (hhs : ∀ t ∈ Ico 0 ε, h t ∈ loewnerStrip δ) :
-- imply
  EqOn g h (Icc 0 ε) := by
-- proof
  apply StatMech.SLE.loewner_solution_unique_of_strip hδ hg0 hh0 hgc hgd hgs hhc hhd hhs

/--
[loewner_solution_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma loewner_solution_unique_eq
  {W : ℝ → ℝ}
  {ε : ℝ}
  {z : ℂ}
  {g h : ℝ → ℂ}
-- given
  (hε : 0 < ε)
  (hg0 : g 0 = z)
  (hh0 : h 0 = z)
  (hgc : ContinuousOn g (Icc 0 ε))
  (hgd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
  (hgu : ∀ t ∈ Icc 0 ε, 0 < (g t).im)
  (hhc : ContinuousOn h (Icc 0 ε))
  (hhd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t)
  (hhu : ∀ t ∈ Icc 0 ε, 0 < (h t).im) :
-- imply
  EqOn g h (Icc 0 ε) := by
-- proof
  apply StatMech.SLE.loewner_solution_unique hε hg0 hh0 hgc hgd hgu hhc hhd hhu

/--
[loewner_local_existsUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerExistence.lean)
-/
@[path]
private lemma loewner_local_existsUnique_eq
  {W : ℝ → ℝ}
  {z : ℂ}
-- given
  (hW : Continuous W)
  (hz : 0 < z.im) :
-- imply
  ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, (g 0 = z ∧ (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt g (loewnerField W t (g t)) (Icc (0 : ℝ) ε) t) ∧ (∀ t ∈ Icc (0 : ℝ) ε, g t ∈ upperHalfPlane)) ∧ ∀ h : ℝ → ℂ, h 0 = z → ContinuousOn h (Icc 0 ε) → (∀ t ∈ Ico 0 ε, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t) → (∀ t ∈ Icc 0 ε, h t ∈ upperHalfPlane) → EqOn g h (Icc 0 ε) := by
-- proof
  apply StatMech.SLE.loewner_local_existsUnique hW hz


-- created on 2026-10-23
