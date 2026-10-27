import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.VarGapProve
open Finset Real Set StatMech StatMech.Probability


/--
[vgp_val_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_val_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {b : Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_val b = p + ptn_sigma p * ptn_psi p b := by
-- proof
  apply StatMech.Probability.vgp_val_eq hp0 hp1 b

/--
[vgp_dictator_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_dictator_expansion_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {e₀ : ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (fun ω : ConfigSpace ι => if (fun ω => ω e₀) ω then (1 : ℝ) else 0) = fun ω => p * ptn_pchar p (∅ : Finset ι) ω + ptn_sigma p * ptn_pchar p ({e₀} : Finset ι) ω := by
-- proof
  apply StatMech.Probability.vgp_dictator_expansion hp0 hp1 e₀

/--
[vgp_dictator_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_dictator_coeff_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {e₀ : ι}
  {S : Finset ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_coeff p (fun ω : ConfigSpace ι => if (fun ω => ω e₀) ω then (1 : ℝ) else 0) S = if S = (∅ : Finset ι) then p else if S = {e₀} then ptn_sigma p else 0 := by
-- proof
  apply StatMech.Probability.vgp_dictator_coeff hp0 hp1 e₀ S

/--
[vgp_dictator_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_dictator_var_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) = p * (1 - p) := by
-- proof
  apply StatMech.Probability.vgp_dictator_var hp0 hp1

/--
[vgp_dictator_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_dictator_totalInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  totalInfl (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) = 1 := by
-- proof
  apply StatMech.Probability.vgp_dictator_totalInfl hp0 hp1

/--
[vgp_maxInfl_eq_totalInfl_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_maxInfl_eq_totalInfl_fin1_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace (Fin 1) → Bool} :
-- imply
  maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp_maxInfl_eq_totalInfl_fin1 p φ

/--
[vgp_dictator_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_dictator_maxInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  maxInfl (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) = 1 := by
-- proof
  apply StatMech.Probability.vgp_dictator_maxInfl hp0 hp1

/--
[vgp_dictator_meanVar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_dictator_meanVar_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) = p * (1 - p) := by
-- proof
  apply StatMech.Probability.vgp_dictator_meanVar hp0 hp1

/--
[vgp_dictator_level1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_dictator_level1_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => S.card = 1), (ptn_coeff p (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) S) ^ 2 = p * (1 - p) := by
-- proof
  apply StatMech.Probability.vgp_dictator_level1 hp0 hp1

/--
[vgp_varPowerCore_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_varPowerCore_refutable_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (hq : 1 / 2 < q) :
-- imply
  ¬ vgc_VarPowerCore q := by
-- proof
  apply StatMech.Probability.vgp_varPowerCore_refutable hq

/--
[vgp_varGapCore_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_varGapCore_refutable_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (hq : 1 / 2 < q) :
-- imply
  ¬ bkt2p_VarGapCore q := by
-- proof
  apply StatMech.Probability.vgp_varGapCore_refutable hq

/--
[vgp_poincare_tight_on_dictator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_poincare_tight_on_dictator_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) = (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp_poincare_tight_on_dictator hp0 hp1

/--
[vgp_master_holds_on_dictator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_master_holds_on_dictator_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (_hu0 : 0 < u)
  (_hu1 : u < 1) :
-- imply
  (∑ S : Finset (Fin 1), 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgp_master_holds_on_dictator hp0 hp1 _hu0 _hu1

/--
[vgp_rhoOptimise_of_openResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_rhoOptimise_of_openResidue_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : frh_openResidue q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.vgp_rhoOptimise_of_openResidue H

/--
[vgp_integral_collapse_logGain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapProve.lean)
-/
@[path]
private lemma vgp_integral_collapse_logGain_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype E]
  {c : E → ℝ}
  {d : E → ℕ}
  {δ : ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i)
  (hδ : 0 ≤ δ)
  (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → (∑ i : E, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i) ≤ δ ^ (u / (2 - u)) * (∑ i : E, 4 * (d i : ℝ) * c i)) :
-- imply
  2 * (∑ i ∈ univ.filter (fun i => d i ≠ 0), c i) * Real.log (1 / δ) ≤ ∑ i : E, 4 * (d i : ℝ) * c i := by
-- proof
  apply StatMech.Probability.vgp_integral_collapse_logGain hc hδ Hmaster


-- created on 2026-10-23
