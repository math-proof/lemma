import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.KKLWire.Part2
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[kklw_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_weight_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {ω : ConfigSpace E} :
-- imply
  OSSS.weight (OSSS.bernoulliWeight p) ω = StatMech.configWeight p ω := by
-- proof
  apply StatMech.TwoDim.kklw_weight_eq p ω

/--
[kklw_prob_eq_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_prob_eq_expect_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  StatMech.prob p A = OSSS.expect (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) := by
-- proof
  apply StatMech.TwoDim.kklw_prob_eq_expect p A

/--
[kklw_influence_eq_infl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_influence_eq_infl_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E} :
-- imply
  StatMech.BeffaraDC.influence p A e = OSSS.infl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) e := by
-- proof
  apply StatMech.TwoDim.kklw_influence_eq_infl p A e

/--
[kklw_sum_influence_eq_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_sum_influence_eq_totalInfl_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  ∑ e, StatMech.BeffaraDC.influence p A e = totalInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) := by
-- proof
  apply StatMech.TwoDim.kklw_sum_influence_eq_totalInfl p A

/--
[kklw_decide_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_decide_eq_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)] :
-- imply
  (fun ω => if (decide (ω ∈ A)) then (1:ℝ) else 0) = A.indicator (fun _ => (1:ℝ)) := by
-- proof
  apply StatMech.TwoDim.kklw_decide_eq_indicator A

/--
[kklw_var_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_var_eq_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)] :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) = StatMech.prob p A * (1 - StatMech.prob p A) := by
-- proof
  apply StatMech.TwoDim.kklw_var_eq p A

/--
[kklw_hkkl_of_hypercontractive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_hkkl_of_hypercontractive_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {H : KKLHypercontractive p 2}
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)] :
-- imply
  2 * (StatMech.prob p A * (1 - StatMech.prob p A)) * kklw_logMaxInfl p A ≤ ∑ e, StatMech.BeffaraDC.influence p A e := by
-- proof
  apply StatMech.TwoDim.kklw_hkkl_of_hypercontractive H A

/--
[kklw_hkkl_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_hkkl_half_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)] :
-- imply
  2 * (StatMech.prob (1/2) A * (1 - StatMech.prob (1/2) A)) * kklw_logMaxInfl (1/2) A ≤ ∑ e, StatMech.BeffaraDC.influence (1/2) A e := by
-- proof
  apply StatMech.TwoDim.kklw_hkkl_half A

/--
[kklw_hkkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_hkkl_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q : ℝ}
-- given
  (Hbkkkl : ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q), KKLHypercontractive p 2) :
-- imply
  ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q), 2 * (StatMech.prob p A * (1 - StatMech.prob p A)) * kklw_logMaxInfl p A ≤ ∑ e, StatMech.BeffaraDC.influence p A e := by
-- proof
  apply StatMech.TwoDim.kklw_hkkl A Hbkkkl

/--
[kklw_sharpThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_sharpThreshold_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q v₀ L : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (Hbkkkl : ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q), KKLHypercontractive p 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ kklw_logMaxInfl p A) :
-- imply
  1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A := by
-- proof
  apply StatMech.TwoDim.kklw_sharpThreshold A hA hq hv0 hL hhalf Hbkkkl hvar hLL'

/--
[kklw_sharpThreshold_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean)
-/
@[path]
private lemma kklw_sharpThreshold_window_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q v₀ L ε : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hM : 0 < 2 * v₀ * L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (Hbkkkl : ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q), KKLHypercontractive p 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ kklw_logMaxInfl p A)
  (hnotyet : StatMech.prob q A ≤ 1 - ε) :
-- imply
  q - 1 / 2 ≤ (1 / 2 - ε) / (2 * v₀ * L) := by
-- proof
  apply StatMech.TwoDim.kklw_sharpThreshold_window A hA hq hM hhalf hv0 hL Hbkkkl hvar hLL' hnotyet


-- created on 2026-10-23
