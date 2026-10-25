import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc34resummation
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc34_spinProd_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_spinProd_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : StatMech.ConfigSpace V} :
-- imply
  StatMech.Ising.spinProd A s ≤ 1 := by
-- proof
  apply StatMech.Walls.gc34_spinProd_le_one G A s

/--
[gc34_expectationJ_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_expectationJ_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  StatMech.Sharpness.expectationJ G β J A ≤ 1 := by
-- proof
  apply StatMech.Walls.gc34_expectationJ_le_one G β J A

/--
[gc34_resummation_factor_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_resummation_factor_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J S) A ∧ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J S) A ≤ 1 := by
-- proof
  apply StatMech.Walls.gc34_resummation_factor_mem_Icc G β J hβ hJ S A

/--
[gc34_sourceClusterResummation_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_sourceClusterResummation_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc33_SourceClusterResummation gc33_G 1 gc33_J gc33_M ∅ 0 1 2 := by
-- proof
  apply StatMech.Walls.gc34_sourceClusterResummation_witness G

/--
[gc34_witness_closes_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_witness_closes_surgery_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc31_MassDoublingSurgery gc33_G 1 gc33_J gc33_M ∅ 0 1 2 := by
-- proof
  apply StatMech.Walls.gc34_witness_closes_surgery G

/--
[gc34_mass_summand_cut_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_mass_summand_cut_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m K : Sharpness.Current V}
  [DecidablePred p]
-- given
  (p : Sym2 V → Prop) :
-- imply
  Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e) = (Sharpness.weight G β J (StatMech.Ising.restrictCut K p) * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e) p)) * (Sharpness.weight G β J (StatMech.Ising.restrictCut K (fun e => ¬ p e)) * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e) (fun e => ¬ p e))) := by
-- proof
  apply StatMech.Walls.gc34_mass_summand_cut_factor G G β J m K p

/--
[gc34_sourceClusterResummation_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_sourceClusterResummation_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V} :
-- imply
  gc33_SourceClusterResummation G β J M B o x y ↔ ∃ (μ : ℝ) (Ψ : Sharpness.Current V → Sharpness.Current V), 0 < μ ∧ μ ≤ 1 ∧ (∀ m ∈ bbr_allFilter G M o x y, Ψ m ∈ bbr_noneFilter G M o x y) ∧ Set.InjOn Ψ (bbr_allFilter G M o x y) ∧ (∀ m ∈ bbr_allFilter G M o x y, 2 * hnw_mass G β J m B ≤ μ * hnw_mass G β J (Ψ m) B) := by
-- proof
  apply StatMech.Walls.gc34_sourceClusterResummation_iff G G β J M B o x y

/--
[gc34_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc34resummation.lean)
-/
@[path]
private lemma gc34_status_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (gc33_SourceClusterResummation G β J M B o x y → gc31_MassDoublingSurgery G β J M B o x y) ∧ (∀ A : Finset V, 0 ≤ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J A) {o, x} ∧ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J A) {o, x} ≤ 1) := by
-- proof
  apply StatMech.Walls.gc34_status G G β J hβ hJ M B o x y


-- created on 2026-10-23
