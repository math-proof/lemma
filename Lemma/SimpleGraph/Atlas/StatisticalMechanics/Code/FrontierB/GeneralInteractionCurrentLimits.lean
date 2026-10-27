import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part7
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[SummableFerromagneticInteraction.row_comp_addLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma row_comp_addLeft_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {x : Site d} :
-- imply
  (fun y => I.coupling s(x, y)) ∘ Equiv.addLeft x = fun y => I.coupling s((0 : Site d), y) := by
-- proof
  apply StatMech.FrontierB.SummableFerromagneticInteraction.row_comp_addLeft I x

/--
[SummableFerromagneticInteraction.row_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma row_summable_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {x : Site d} :
-- imply
  Summable (fun y => I.coupling s(x, y)) := by
-- proof
  apply StatMech.FrontierB.SummableFerromagneticInteraction.row_summable I x

/--
[SummableFerromagneticInteraction.row_tsum_eq_strength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma row_tsum_eq_strength_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {x : Site d} :
-- imply
  (∑' y, I.coupling s(x, y)) = I.strength := by
-- proof
  apply StatMech.FrontierB.SummableFerromagneticInteraction.row_tsum_eq_strength I x

/--
[SummableFerromagneticInteraction.strength_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma strength_nonneg_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d} :
-- imply
  0 <= I.strength := by
-- proof
  apply StatMech.FrontierB.SummableFerromagneticInteraction.strength_nonneg I

/--
[SummableFerromagneticInteraction.coupling_le_strength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma coupling_le_strength_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {e : Sym2 (Site d)} :
-- imply
  I.coupling e <= I.strength := by
-- proof
  apply StatMech.FrontierB.SummableFerromagneticInteraction.coupling_le_strength I e

/--
[mem_interactionBoxVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma mem_interactionBoxVertices_eq
  {d n : Nat}
  {x : Site d} :
-- imply
  x ∈ interactionBoxVertices d n ↔ x ∈ box d n := by
-- proof
  apply StatMech.FrontierB.mem_interactionBoxVertices

/--
[interactionBoxEdgeIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma interactionBoxEdgeIncl_injective_eq
  {d n : Nat} :
-- imply
  Function.Injective (interactionBoxEdgeIncl d n) := by
-- proof
  apply StatMech.FrontierB.interactionBoxEdgeIncl_injective d n

/--
[extendInteractionBoxCurrent_included](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma extendInteractionBoxCurrent_included_eq
  {d n : Nat}
  {m : EdgeCurrent (interactionBoxGraph d n)}
  {e : (interactionBoxGraph d n).edgeFinset} :
-- imply
  extendInteractionBoxCurrent d n m (interactionBoxEdgeIncl d n e) = m e := by
-- proof
  apply StatMech.FrontierB.extendInteractionBoxCurrent_included d n m e

/--
[extendInteractionBoxCurrent_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma extendInteractionBoxCurrent_outside_eq
  {d n : Nat}
  {m : EdgeCurrent (interactionBoxGraph d n)}
  {e : Sym2 (Site d)}
-- given
  (he : e ∉ Set.range (interactionBoxEdgeIncl d n)) :
-- imply
  extendInteractionBoxCurrent d n m e = 0 := by
-- proof
  apply StatMech.FrontierB.extendInteractionBoxCurrent_outside d n m e he

/--
[measurable_extendInteractionBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma measurable_extendInteractionBoxCurrent_eq
  {d n : Nat} :
-- imply
  Measurable (extendInteractionBoxCurrent d n) := by
-- proof
  apply StatMech.FrontierB.measurable_extendInteractionBoxCurrent d n

/--
[generalFreeBoxCurrentMeasure_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_edge_tail_eq
  {d : Nat}
  {n : Nat}
  {beta : Real}
  {e : (interactionBoxGraph d n).edgeFinset}
  {K : Nat}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta) :
-- imply
  (generalFreeBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m (interactionBoxEdgeIncl d n e)} = (sourcelessCurrentMeasure (interactionBoxGraph d n) beta (interactionBoxCoupling J n) hbeta (fun e => hJ (Sym2.map Subtype.val e)) : Measure (EdgeCurrent (interactionBoxGraph d n))) {m | K <= m e} := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_edge_tail J hJ n beta hbeta e K

/--
[generalPlusBoxCurrentMeasure_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_edge_tail_eq
  {d : Nat}
  {n : Nat}
  {beta : Real}
  {e : (interactionBoxGraph d (2 * n + 1)).edgeFinset}
  {K : Nat}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta) :
-- imply
  (generalPlusBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m (interactionBoxEdgeIncl d (2 * n + 1) e)} = (boundaryCurrentMeasure (interactionBoxGraph d (2 * n + 1)) beta (interactionBoxCoupling J (2 * n + 1)) hbeta (fun e => hJ (Sym2.map Subtype.val e)) (interactionPlusInterior d n) : Measure (EdgeCurrent (interactionBoxGraph d (2 * n + 1)))) {m | K <= m e} := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_edge_tail J hJ n beta hbeta e K

/--
[generalFreeBoxCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_edge_inverse_tail_le_eq
  {d : Nat}
  {n : Nat}
  {beta : Real}
  {e : Sym2 (Site d)}
  {K : Nat}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta)
  (hK : 0 < K) :
-- imply
  (generalFreeBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <= ENNReal.ofReal (Real.exp (beta * J e)) / K := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_edge_inverse_tail_le J hJ n beta hbeta e K hK

/--
[generalPlusBoxCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_edge_inverse_tail_le_eq
  {d : Nat}
  {n : Nat}
  {beta : Real}
  {e : Sym2 (Site d)}
  {K : Nat}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta)
  (hK : 0 < K) :
-- imply
  (generalPlusBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <= ENNReal.ofReal (Real.exp (beta * J e)) / K := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_edge_inverse_tail_le J hJ n beta hbeta e K hK

/--
[generalFreeBoxCurrentMeasure_uniform_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_uniform_inverse_tail_le_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {n : Nat}
  {beta : Real}
  {e : Sym2 (Site d)}
  {K : Nat}
-- given
  (hbeta : 0 <= beta)
  (hK : 0 < K) :
-- imply
  (generalFreeBoxCurrentMeasure I.coupling I.nonneg n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <= ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_uniform_inverse_tail_le I n beta hbeta e K hK

/--
[generalPlusBoxCurrentMeasure_uniform_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_uniform_inverse_tail_le_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {n : Nat}
  {beta : Real}
  {e : Sym2 (Site d)}
  {K : Nat}
-- given
  (hbeta : 0 <= beta)
  (hK : 0 < K) :
-- imply
  (generalPlusBoxCurrentMeasure I.coupling I.nonneg n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <= ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_uniform_inverse_tail_le I n beta hbeta e K hK

/--
[generalFreeBoxCurrentMeasure_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_tight_eq
  {d : Nat}
  {beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta) :
-- imply
  IsTightMeasureSet (Set.range fun n => (generalFreeBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_tight J hJ beta hbeta

/--
[generalPlusBoxCurrentMeasure_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_tight_eq
  {d : Nat}
  {beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta) :
-- imply
  IsTightMeasureSet (Set.range fun n => (generalPlusBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_tight J hJ beta hbeta

/--
[generalFreePlusBoxCurrentMeasure_joint_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalFreePlusBoxCurrentMeasure_joint_subsequence_eq
  {d : Nat}
  {beta : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 <= J e)
  (hbeta : 0 <= beta) :
-- imply
  ∃ (nuFree nuPlus : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : Nat -> Nat), StrictMono phi ∧ WeakCurrentConverges ((fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta) ∘ phi) nuFree ∧ WeakCurrentConverges ((fun n => generalPlusBoxCurrentMeasure J hJ n beta hbeta) ∘ phi) nuPlus := by
-- proof
  apply StatMech.FrontierB.generalFreePlusBoxCurrentMeasure_joint_subsequence J hJ beta hbeta

/--
[generalCurrentBoxSubsequence_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalCurrentBoxSubsequence_strictMono_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : Real}
-- given
  (hbeta : 0 <= beta) :
-- imply
  StrictMono (generalCurrentBoxSubsequence I beta hbeta) := by
-- proof
  apply StatMech.FrontierB.generalCurrentBoxSubsequence_strictMono I beta hbeta

/--
[generalFreeBoxCurrentMeasure_tendsto_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_tendsto_infinite_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : Real}
-- given
  (hbeta : 0 <= beta) :
-- imply
  WeakCurrentConverges ((fun n => generalFreeBoxCurrentMeasure I.coupling I.nonneg n beta hbeta) ∘ generalCurrentBoxSubsequence I beta hbeta) (generalInfiniteFreeCurrentMeasure I beta hbeta) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_tendsto_infinite I beta hbeta

/--
[generalPlusBoxCurrentMeasure_tendsto_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_tendsto_infinite_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : Real}
-- given
  (hbeta : 0 <= beta) :
-- imply
  WeakCurrentConverges ((fun n => generalPlusBoxCurrentMeasure I.coupling I.nonneg n beta hbeta) ∘ generalCurrentBoxSubsequence I beta hbeta) (generalInfinitePlusCurrentMeasure I beta hbeta) := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_tendsto_infinite I beta hbeta

/--
[generalFreeBoxCurrentMeasure_cylinder_tendsto_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalFreeBoxCurrentMeasure_cylinder_tendsto_infinite_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 <= beta)
  (A : Set (S -> Nat)) :
-- imply
  Tendsto (fun k => generalFreeBoxCurrentMeasure I.coupling I.nonneg (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta (currentCylinder S A)) atTop (nhds (generalInfiniteFreeCurrentMeasure I beta hbeta (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.generalFreeBoxCurrentMeasure_cylinder_tendsto_infinite I beta hbeta S A

/--
[generalPlusBoxCurrentMeasure_cylinder_tendsto_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_cylinder_tendsto_infinite_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : Real}
  {S : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 <= beta)
  (A : Set (S -> Nat)) :
-- imply
  Tendsto (fun k => generalPlusBoxCurrentMeasure I.coupling I.nonneg (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta (currentCylinder S A)) atTop (nhds (generalInfinitePlusCurrentMeasure I beta hbeta (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_cylinder_tendsto_infinite I beta hbeta S A

/--
[generalInteractionCurrentSubsequencePackage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean)
-/
@[path]
private lemma generalInteractionCurrentSubsequencePackage_eq
  {d : Nat}
  {I : SummableFerromagneticInteraction d}
  {beta : Real}
-- given
  (hbeta : 0 <= beta) :
-- imply
  GeneralInteractionCurrentSubsequencePackage I beta hbeta where subsequence_strict := by
-- proof
  apply StatMech.FrontierB.generalInteractionCurrentSubsequencePackage I beta hbeta


-- created on 2026-10-23
