import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.KestenThresholdRoute
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[ktr_variance_lb_of_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_variance_lb_of_crossing_eq
  [Fintype E]
  [DecidableEq E]
  {x δ : ℝ}
-- given
  (hl : δ ≤ x)
  (hr : x ≤ 1 - δ) :
-- imply
  δ * (1 - δ) ≤ x * (1 - x) := by
-- proof
  apply StatMech.TwoDim.ktr_variance_lb_of_crossing hl hr

/--
[ktr_prob_variance_lb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_prob_variance_lb_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p δ : ℝ}
-- given
  (hl : δ ≤ prob p A)
  (hr : prob p A ≤ 1 - δ) :
-- imply
  δ * (1 - δ) ≤ prob p A * (1 - prob p A) := by
-- proof
  apply StatMech.TwoDim.ktr_prob_variance_lb A hl hr

/--
[ktr_totalInfluence_eq_card_mul_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_totalInfluence_eq_card_mul_of_symmetric_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p ι : ℝ}
-- given
  (hsym : ∀ e : E, influence p A e = ι) :
-- imply
  ∑ e, influence p A e = (Fintype.card E : ℝ) * ι := by
-- proof
  apply StatMech.TwoDim.ktr_totalInfluence_eq_card_mul_of_symmetric A hsym

/--
[ktr_maxInfluence_eq_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_maxInfluence_eq_of_symmetric_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p ι : ℝ}
  {e : E}
-- given
  (hsym : ∀ e : E, influence p A e = ι) :
-- imply
  influence p A e = ι := by
-- proof
  apply StatMech.TwoDim.ktr_maxInfluence_eq_of_symmetric A hsym e

/--
[ktr_totalInfluence_lb_of_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_totalInfluence_lb_of_window_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q Δ : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 < q)
  (hΔ : prob (1 / 2) A + Δ < prob q A) :
-- imply
  ∃ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), Δ / (q - 1 / 2) ≤ ∑ e, influence p A e := by
-- proof
  apply StatMech.TwoDim.ktr_totalInfluence_lb_of_window A hA hq hΔ

/--
[ktr_totalInfluence_lb_of_kkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_totalInfluence_lb_of_kkl_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p C v₀ L L' : ℝ}
-- given
  (hC : 0 < C)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hkkl : C * (prob p A * (1 - prob p A)) * L' ≤ ∑ e, influence p A e)
  (hvar : v₀ ≤ prob p A * (1 - prob p A))
  (hLL' : L ≤ L') :
-- imply
  C * v₀ * L ≤ ∑ e, influence p A e := by
-- proof
  apply StatMech.TwoDim.ktr_totalInfluence_lb_of_kkl A hC hv0 hL hkkl hvar hLL'

/--
[ktr_hinfl_of_kkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_hinfl_of_kkl_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q C v₀ L : ℝ}
  {L' : ℝ → ℝ}
-- given
  (hC : 0 < C)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hkkl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), C * (prob p A * (1 - prob p A)) * L' p ≤ ∑ e, influence p A e)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ prob p A * (1 - prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ L' p) :
-- imply
  ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), C * v₀ * L ≤ ∑ e, influence p A e := by
-- proof
  apply StatMech.TwoDim.ktr_hinfl_of_kkl A hC hv0 hL L' hkkl hvar hLL'

/--
[ktr_sharpThreshold_via_kkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_sharpThreshold_via_kkl_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q C v₀ L : ℝ}
  {L' : ℝ → ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hC : 0 < C)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hhalf : prob (1 / 2) A = 1 / 2)
  (hkkl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), C * (prob p A * (1 - prob p A)) * L' p ≤ ∑ e, influence p A e)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ prob p A * (1 - prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ L' p) :
-- imply
  1 / 2 + (C * v₀ * L) * (q - 1 / 2) ≤ prob q A := by
-- proof
  apply StatMech.TwoDim.ktr_sharpThreshold_via_kkl A hA hq hC hv0 hL hhalf L' hkkl hvar hLL'

/--
[ktr_sharpThreshold_window_via_kkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenThresholdRoute.lean)
-/
@[path]
private lemma ktr_sharpThreshold_window_via_kkl_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q C v₀ L ε : ℝ}
  {L' : ℝ → ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hM : 0 < C * v₀ * L)
  (hhalf : prob (1 / 2) A = 1 / 2)
  (hC : 0 < C)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hkkl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), C * (prob p A * (1 - prob p A)) * L' p ≤ ∑ e, influence p A e)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ prob p A * (1 - prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ L' p)
  (hnotyet : prob q A ≤ 1 - ε) :
-- imply
  q - 1 / 2 ≤ (1 / 2 - ε) / (C * v₀ * L) := by
-- proof
  apply StatMech.TwoDim.ktr_sharpThreshold_window_via_kkl A hA hq hM hhalf hC hv0 hL L' hkkl hvar hLL' hnotyet


-- created on 2026-10-23
