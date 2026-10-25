import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentFormalAssembly.Part2
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraphFormalEvenPolynomial_eq_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalEvenPolynomial_eq_coe_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  kwGraphFormalEvenPolynomial G = (kwGraphEvenMvPolynomial G : MvPowerSeries (Sym2 V) ℂ) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalEvenPolynomial_eq_coe G

/--
[kwGraphFormalEvenPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalEvenPolynomial_eval_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ} :
-- imply
  ons_mvSeriesEval (kwGraphFormalEvenPolynomial G) weight = kwEvenPolynomial G weight := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalEvenPolynomial_eval G weight

/--
[kwCycleComponentSeries_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwCycleComponentSeries_coeff_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  {G : SimpleGraph V}
  {base : I → V}
  {cycle : (i : I) → G.Walk (base i) (base i)}
  {m : Sym2 V →₀ ℕ} :
-- imply
  MvPowerSeries.coeff m (kwCycleComponentSeries base cycle) = ∑ i : I, if ons_finsetExponent (cycle i).edges.toFinset = m then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.kwCycleComponentSeries_coeff base cycle m

/--
[kwCycleComponentSeries_coeff_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwCycleComponentSeries_coeff_piece_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  {G : SimpleGraph V}
  {base : I → V}
  {cycle : (i : I) → G.Walk (base i) (base i)}
  {j : I}
-- given
  (hcycle : ∀ i, (cycle i).IsCycle)
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (cycle i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent (cycle j).edges.toFinset) (kwCycleComponentSeries base cycle) = 1 := by
-- proof
  apply StatMech.FrontierA.kwCycleComponentSeries_coeff_piece base cycle hcycle hdisj j

/--
[kwCycleComponentSeries_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwCycleComponentSeries_hasSubst_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  {G : SimpleGraph V}
  {base : I → V}
  {cycle : (i : I) → G.Walk (base i) (base i)}
-- given
  (hcycle : ∀ i, (cycle i).IsCycle) :
-- imply
  PowerSeries.HasSubst (kwCycleComponentSeries base cycle) := by
-- proof
  apply StatMech.FrontierA.kwCycleComponentSeries_hasSubst base cycle hcycle

/--
[kwGraphFormalLog_coeff_eq_cycleComponent_of_antidiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalLog_coeff_eq_cycleComponent_of_antidiag_eq
  {V I : Type u}
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq K]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {S : Finset (Sym2 V)}
  {base : I → V}
  {cycle : (i : I) → G.Walk (base i) (base i)}
  {T : Finset K}
  {g : K →₀ Sym2 V →₀ ℕ}
  {i : K}
-- given
  (hunit : KWGraphUnitCycleLog G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hS : S ∈ evenSubgraphs G)
  (hcycle : ∀ i, (cycle i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (cycle i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (cycle i).edges.toFinset))
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T) :
-- imply
  kwGraphFormalLogCoeff G phase (g i) = MvPowerSeries.coeff (g i) (kwCycleComponentSeries base cycle) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLog_coeff_eq_cycleComponent_of_antidiag G phase hunit hdeg S hS base cycle hcycle hcover hdisj T g hg hi

/--
[kwMvPowerSeries_coeff_pow_eq_of_antidiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwMvPowerSeries_coeff_pow_eq_of_antidiag_eq
  [DecidableEq E]
  {left right : MvPowerSeries E ℂ}
  {m : E →₀ ℕ}
  {n : ℕ}
-- given
  (hcoeff : ∀ (g : ℕ →₀ E →₀ ℕ), g ∈ (Finset.range n).finsuppAntidiag m → ∀ i ∈ Finset.range n, MvPowerSeries.coeff (g i) left = MvPowerSeries.coeff (g i) right) :
-- imply
  MvPowerSeries.coeff m (left ^ n) = MvPowerSeries.coeff m (right ^ n) := by
-- proof
  apply StatMech.FrontierA.kwMvPowerSeries_coeff_pow_eq_of_antidiag left right m n hcoeff

/--
[kwCycleComponentSeries_pow_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwCycleComponentSeries_pow_coeff_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  {G : SimpleGraph V}
  {S : Finset (Sym2 V)}
  {base : I → V}
  {cycle : (i : I) → G.Walk (base i) (base i)}
  {n : ℕ}
-- given
  (hcycle : ∀ i, (cycle i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (cycle i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (cycle i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) ((kwCycleComponentSeries base cycle) ^ n) = if n = Fintype.card I then (n.factorial : ℂ) else 0 := by
-- proof
  apply StatMech.FrontierA.kwCycleComponentSeries_pow_coeff S base cycle hcycle hcover hdisj n

/--
[kwCycleComponentExp_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwCycleComponentExp_coeff_eq
  {V I : Type u}
  [DecidableEq V]
  [Fintype I]
  {G : SimpleGraph V}
  {S : Finset (Sym2 V)}
  {base : I → V}
  {cycle : (i : I) → G.Walk (base i) (base i)}
-- given
  (hcycle : ∀ i, (cycle i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (cycle i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (cycle i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (PowerSeries.subst (kwCycleComponentSeries base cycle) (PowerSeries.exp ℂ)) = 1 := by
-- proof
  apply StatMech.FrontierA.kwCycleComponentExp_coeff S base cycle hcycle hcover hdisj

/--
[kwGraphFormalRoot_coeff_evenSubgraph_of_unitCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_coeff_evenSubgraph_of_unitCycleLog_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {S : Finset (Sym2 V)}
-- given
  (hunit : KWGraphUnitCycleLog G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hS : S ∈ evenSubgraphs G) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (kwGraphFormalRoot G phase) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_coeff_evenSubgraph_of_unitCycleLog G phase hunit hdeg S hS

/--
[kwGraphLoopExponent_apply_eq_zero_of_not_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphLoopExponent_apply_eq_zero_of_not_mem_edgeFinset_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart}
  {edge : Sym2 V}
-- given
  (hedge : edge ∉ G.edgeFinset) :
-- imply
  kwGraphLoopExponent G loop edge = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopExponent_apply_eq_zero_of_not_mem_edgeFinset G loop edge hedge

/--
[kwGraphFormalLogCoeff_eq_zero_of_offGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_eq_zero_of_offGraph_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {m : Sym2 V →₀ ℕ}
  {edge : Sym2 V}
-- given
  (hedge : edge ∉ G.edgeFinset)
  (hmedge : m edge ≠ 0) :
-- imply
  kwGraphFormalLogCoeff G phase m = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_eq_zero_of_offGraph G phase m edge hedge hmedge

/--
[kwGraphFormalRoot_coeff_eq_zero_of_offGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_coeff_eq_zero_of_offGraph_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {m : Sym2 V →₀ ℕ}
  {edge : Sym2 V}
-- given
  (hedge : edge ∉ G.edgeFinset)
  (hmedge : m edge ≠ 0) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_coeff_eq_zero_of_offGraph G phase m edge hedge hmedge

/--
[kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {S : Finset (Sym2 V)}
-- given
  (hunit : KWGraphUnitCycleLog G phase)
  (hS : S ∉ evenSubgraphs G) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (kwGraphFormalRoot G phase) = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even G phase hunit S hS

/--
[kwGraphFormalEvenPolynomial_coeff_finsetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalEvenPolynomial_coeff_finsetExponent_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)} :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (kwGraphFormalEvenPolynomial G) = if S ∈ evenSubgraphs G then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalEvenPolynomial_coeff_finsetExponent G S

/--
[kwGraphFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Sym2 V →₀ ℕ}
-- given
  (hm : ¬ ons_IsSquarefreeExponent m) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalEvenPolynomial G) = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree G m hm

/--
[kwGraphFormalRoot_eq_evenPolynomial_of_unitCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kwGraphFormalRoot_eq_evenPolynomial_of_unitCycleLog_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
-- given
  (hunit : KWGraphUnitCycleLog G phase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hnonsquare : ∀ m : Sym2 V →₀ ℕ, ¬ ons_IsSquarefreeExponent m → MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
-- imply
  kwGraphFormalRoot G phase = kwGraphFormalEvenPolynomial G := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalRoot_eq_evenPolynomial_of_unitCycleLog G phase hunit hdeg hnonsquare

/--
[kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_unitCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_unitCycleLog_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hunit : KWGraphUnitCycleLog G embedding.turnPhase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
-- imply
  kwGraphFormalRoot G embedding.turnPhase = kwGraphFormalEvenPolynomial G := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_unitCycleLog G embedding hunit hdeg

/--
[kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_unitCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_unitCycleLog_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hunit : KWGraphUnitCycleLog G embedding.turnPhase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (kwGraphTransition G weight embedding.turnPhase) = kwEvenPolynomial G weight := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_detWalkRoot_eq_evenPolynomial_of_unitCycleLog G embedding hunit hdeg weight q hq hentry hcard

/--
[kacWard_straightLine_trivalent_of_unitCycleLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean)
-/
@[path]
private lemma kacWard_straightLine_trivalent_of_unitCycleLog_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hunit : KWGraphUnitCycleLog G embedding.turnPhase)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_trivalent_of_unitCycleLog G embedding hunit hdeg weight q hq hentry hcard


-- created on 2026-10-23
