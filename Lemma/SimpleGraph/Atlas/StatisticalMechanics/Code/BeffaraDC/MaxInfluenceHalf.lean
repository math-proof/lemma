import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.MaxInfluenceHalf
open Finset Real Set StatMech StatMech.BeffaraDC


/--
[maxInfl_half_ge_var_mul_log_card_div_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluenceHalf.lean)
-/
@[path]
private lemma maxInfl_half_ge_var_mul_log_card_div_card_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool} :
-- imply
  OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ Probability.maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.BeffaraDC.maxInfl_half_ge_var_mul_log_card_div_card φ

/--
[maxInfluence_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluenceHalf.lean)
-/
@[path]
private lemma maxInfluence_half_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)} :
-- imply
  ∃ e : E, StatMech.prob (1 / 2 : ℝ) A * (1 - StatMech.prob (1 / 2 : ℝ) A) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ influence (1 / 2 : ℝ) A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_half A

/--
[exists_influence_pos_half_of_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluenceHalf.lean)
-/
@[path]
private lemma exists_influence_pos_half_of_nontrivial_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
-- given
  (hcard : 2 ≤ Fintype.card E)
  (hprob0 : 0 < StatMech.prob (1 / 2 : ℝ) A)
  (hprob1 : StatMech.prob (1 / 2 : ℝ) A < 1) :
-- imply
  ∃ e : E, 0 < influence (1 / 2 : ℝ) A e := by
-- proof
  apply StatMech.BeffaraDC.exists_influence_pos_half_of_nontrivial A hcard hprob0 hprob1

/--
[maxInfluence_half_of_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluenceHalf.lean)
-/
@[path]
private lemma maxInfluence_half_of_increasing_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
-- given
  (_hA : IsIncreasing A) :
-- imply
  ∃ e : E, StatMech.prob (1 / 2 : ℝ) A * (1 - StatMech.prob (1 / 2 : ℝ) A) * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ) ≤ influence (1 / 2 : ℝ) A e := by
-- proof
  apply StatMech.BeffaraDC.maxInfluence_half_of_increasing A _hA


-- created on 2026-10-23
