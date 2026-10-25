import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalCoefficient.Part3
open StatMech StatMech.Onsager


/--
[ons_finsuppAntidiag_finsetExponent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_finsuppAntidiag_finsetExponent_le_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : Finset I}
  {S : Finset E}
  {g : I →₀ E →₀ ℕ}
  {i : I}
  {edge : E}
-- given
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T) :
-- imply
  g i edge ≤ if edge ∈ S then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_finsuppAntidiag_finsetExponent_le T S g hg hi edge

/--
[ons_finsuppAntidiag_finsetExponent_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_finsuppAntidiag_finsetExponent_component_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : Finset I}
  {S : Finset E}
  {g : I →₀ E →₀ ℕ}
  {i : I}
-- given
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T) :
-- imply
  g i = ons_finsetExponent (g i).support := by
-- proof
  apply StatMech.Onsager.ons_finsuppAntidiag_finsetExponent_component T S g hg hi

/--
[ons_finsuppAntidiag_finsetExponent_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_finsuppAntidiag_finsetExponent_support_subset_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : Finset I}
  {S : Finset E}
  {g : I →₀ E →₀ ℕ}
  {i : I}
-- given
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T) :
-- imply
  (g i).support ⊆ S := by
-- proof
  apply StatMech.Onsager.ons_finsuppAntidiag_finsetExponent_support_subset T S g hg hi

/--
[ons_finsuppAntidiag_finsetExponent_support_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_finsuppAntidiag_finsetExponent_support_disjoint_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : Finset I}
  {S : Finset E}
  {g : I →₀ E →₀ ℕ}
  {i j : I}
-- given
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T)
  (hj : j ∈ T)
  (hij : i ≠ j) :
-- imply
  Disjoint (g i).support (g j).support := by
-- proof
  apply StatMech.Onsager.ons_finsuppAntidiag_finsetExponent_support_disjoint T S g hg hi hj hij

/--
[ons_finsuppAntidiag_finsetExponent_support_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_finsuppAntidiag_finsetExponent_support_cover_eq
  [DecidableEq I]
  [DecidableEq E]
  {T : Finset I}
  {S : Finset E}
  {g : I →₀ E →₀ ℕ}
-- given
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S)) :
-- imply
  S = T.biUnion (fun i ↦ (g i).support) := by
-- proof
  apply StatMech.Onsager.ons_finsuppAntidiag_finsetExponent_support_cover T S g hg

/--
[ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
-- given
  (hne : ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent S) ≠ 0) :
-- imply
  ∃ (root : ons_Dart L) (q : (ons_decGraph L).Walk root root), q.IsCycle ∧ q.snd = ons_dartRev L root ∧ q.edges.toFinset = S ∧ ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (ons_finsetExponent S) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero L a b S hne

/--
[ons_isCycles_cycle_edges_eq_of_common_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_isCycles_cycle_edges_eq_of_common_vertex_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {p : G.Walk u u}
  {q : G.Walk v v}
  {x : V}
-- given
  (hcyc : G.IsCycles)
  (hp : p.IsCycle)
  (hq : q.IsCycle)
  (hxp : x ∈ p.toSubgraph.verts)
  (hxq : x ∈ q.toSubgraph.verts) :
-- imply
  p.edges.toFinset = q.edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_isCycles_cycle_edges_eq_of_common_vertex hcyc p q hp hq hxp hxq

/--
[ons_cycle_edges_eq_decomposition_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_cycle_edges_eq_decomposition_piece_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)}
  [Fintype I]
  [DecidableEq I]
  {base : I → V}
  {p : (i : I) → G.Walk (base i) (base i)}
  {root : V}
  {q : G.Walk root root}
-- given
  (hdeg : ∀ x, G.degree x ≤ 3)
  (hS : S ∈ evenSubgraphs G)
  (hp : ∀ i, (p i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (p i).edges.toFinset))
  (hq : q.IsCycle)
  (hqsub : q.edges.toFinset ⊆ S) :
-- imply
  ∃ i : I, q.edges.toFinset = (p i).edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_cycle_edges_eq_decomposition_piece G hdeg S hS base p hp hcover q hq hqsub

/--
[ons_decFormalLogCoeff_antidiag_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_antidiag_component_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  [Fintype I]
  [DecidableEq I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
  [DecidableEq K]
  {T : Finset K}
  {g : K →₀ ons_DecEdge L →₀ ℕ}
  {i : K}
-- given
  (hS : S ∈ evenSubgraphs (ons_decGraph L))
  (hp : ∀ i, (p i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (p i).edges.toFinset))
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T)
  (hne : ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (g i) ≠ 0) :
-- imply
  ∃ j : I, (g i).support = (p j).edges.toFinset ∧ ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (g i) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (p j))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_antidiag_component L a b S hS base p hp hcover T g hg hi hne

/--
[ons_cycle_edges_toFinset_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_cycle_edges_toFinset_nonempty_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
  {p : G.Walk v v}
-- given
  (hp : p.IsCycle) :
-- imply
  p.edges.toFinset.Nonempty := by
-- proof
  apply StatMech.Onsager.ons_cycle_edges_toFinset_nonempty p hp

/--
[ons_cycle_decomposition_edgeSet_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_cycle_decomposition_edgeSet_injective_eq
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {base : I → V}
  {p : (i : I) → G.Walk (base i) (base i)}
-- given
  (hp : ∀ i, (p i).IsCycle)
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (p i).edges.toFinset)) :
-- imply
  Function.Injective (fun i ↦ (p i).edges.toFinset) := by
-- proof
  apply StatMech.Onsager.ons_cycle_decomposition_edgeSet_injective base p hp hdisj

/--
[ons_decComponentSeries_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decComponentSeries_coeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  [Fintype I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  MvPowerSeries.coeff m (ons_decComponentSeries L a b base p) = ∑ i : I, if ons_finsetExponent (p i).edges.toFinset = m then (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ) else 0 := by
-- proof
  apply StatMech.Onsager.ons_decComponentSeries_coeff L a b base p m

/--
[ons_decComponentSeries_coeff_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decComponentSeries_coeff_piece_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  [Fintype I]
  [DecidableEq I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
  {j : I}
-- given
  (hp : ∀ i, (p i).IsCycle)
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (p i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent (p j).edges.toFinset) (ons_decComponentSeries L a b base p) = (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (p j))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decComponentSeries_coeff_piece L a b base p hp hdisj j

/--
[ons_decFormalLog_coeff_eq_componentSeries_of_antidiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalLog_coeff_eq_componentSeries_of_antidiag_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  [Fintype I]
  [DecidableEq I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
  [DecidableEq K]
  {T : Finset K}
  {g : K →₀ ons_DecEdge L →₀ ℕ}
  {i : K}
-- given
  (hS : S ∈ evenSubgraphs (ons_decGraph L))
  (hp : ∀ i, (p i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (p i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (p i).edges.toFinset))
  (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
  (hi : i ∈ T) :
-- imply
  MvPowerSeries.coeff (g i) (ons_decFormalLog L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = MvPowerSeries.coeff (g i) (ons_decComponentSeries L a b base p) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLog_coeff_eq_componentSeries_of_antidiag L a b S hS base p hp hcover hdisj T g hg hi

/--
[ons_decFormalLog_pow_coeff_eq_componentSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalLog_pow_coeff_eq_componentSeries_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  [Fintype I]
  [DecidableEq I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
  {n : ℕ}
-- given
  (hS : S ∈ evenSubgraphs (ons_decGraph L))
  (hp : ∀ i, (p i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (p i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (p i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) ((ons_decFormalLog L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) ^ n) = MvPowerSeries.coeff (ons_finsetExponent S) ((ons_decComponentSeries L a b base p) ^ n) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLog_pow_coeff_eq_componentSeries L a b S hS base p hp hcover hdisj n

/--
[ons_finsetExponent_biUnion_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_finsetExponent_biUnion_eq_sum_eq
  [DecidableEq E]
  [Fintype I]
  [DecidableEq I]
  {S : Finset E}
  {piece : I → Finset E}
-- given
  (hcover : S = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint piece) :
-- imply
  ons_finsetExponent S = ∑ i, ons_finsetExponent (piece i) := by
-- proof
  apply StatMech.Onsager.ons_finsetExponent_biUnion_eq_sum S piece hcover hdisj

/--
[ons_sum_finsetExponent_eq_iff_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_sum_finsetExponent_eq_iff_bijective_eq
  [DecidableEq E]
  [Fintype I]
  [DecidableEq I]
  {S : Finset E}
  {piece : I → Finset E}
  {n : ℕ}
  {f : Fin n → I}
-- given
  (hcover : S = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint piece)
  (hnonempty : ∀ i, (piece i).Nonempty) :
-- imply
  (∑ k, ons_finsetExponent (piece (f k))) = ons_finsetExponent S ↔ Function.Bijective f := by
-- proof
  apply StatMech.Onsager.ons_sum_finsetExponent_eq_iff_bijective S piece hcover hdisj hnonempty n f

/--
[ons_decComponentSeries_pow_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decComponentSeries_pow_coeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  [Fintype I]
  [DecidableEq I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
  {n : ℕ}
-- given
  (hp : ∀ i, (p i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (p i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (p i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) ((ons_decComponentSeries L a b base p) ^ n) = if n = Fintype.card I then (n.factorial : ℂ) * ∏ i, (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ) else 0 := by
-- proof
  apply StatMech.Onsager.ons_decComponentSeries_pow_coeff L a b S base p hp hcover hdisj n

/--
[ons_decComponentSeries_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decComponentSeries_hasSubst_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  [Fintype I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
-- given
  (hp : ∀ i, (p i).IsCycle) :
-- imply
  PowerSeries.HasSubst (ons_decComponentSeries L a b base p) := by
-- proof
  apply StatMech.Onsager.ons_decComponentSeries_hasSubst L a b base p hp

/--
[ons_decFormalRoot_coeff_eq_componentExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_eq_componentExp_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  [Fintype I]
  [DecidableEq I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
-- given
  (hS : S ∈ evenSubgraphs (ons_decGraph L))
  (hp : ∀ i, (p i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (p i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (p i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = MvPowerSeries.coeff (ons_finsetExponent S) (PowerSeries.subst (ons_decComponentSeries L a b base p) (PowerSeries.exp ℂ)) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_eq_componentExp L a b S hS base p hp hcover hdisj

/--
[ons_decComponentExp_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decComponentExp_coeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
  [Fintype I]
  [DecidableEq I]
  {base : I → ons_Dart L}
  {p : (i : I) → (ons_decGraph L).Walk (base i) (base i)}
-- given
  (hp : ∀ i, (p i).IsCycle)
  (hcover : S = Finset.univ.biUnion (fun i ↦ (p i).edges.toFinset))
  (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ (p i).edges.toFinset)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (PowerSeries.subst (ons_decComponentSeries L a b base p) (PowerSeries.exp ℂ)) = ∏ i, (ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decComponentExp_coeff L a b S base p hp hcover hdisj

/--
[ons_decFormalRoot_coeff_evenSubgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_evenSubgraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent D.1) (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = (ons_spinCharacter a b (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_evenSubgraph L a b D

/--
[ons_evenSubgraphs_biUnion_of_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_evenSubgraphs_biUnion_of_pairwiseDisjoint_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq I]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {T : Finset I}
  {piece : I → Finset (Sym2 V)}
-- given
  (hdisj : (T : Set I).PairwiseDisjoint piece)
  (hpiece : ∀ i ∈ T, piece i ∈ evenSubgraphs G) :
-- imply
  T.biUnion piece ∈ evenSubgraphs G := by
-- proof
  apply StatMech.Onsager.ons_evenSubgraphs_biUnion_of_pairwiseDisjoint G T piece hdisj hpiece

/--
[ons_decFormalRoot_coeff_squarefree_eq_zero_of_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_squarefree_eq_zero_of_not_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
-- given
  (hS : S ∉ evenSubgraphs (ons_decGraph L)) :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_squarefree_eq_zero_of_not_even L a b S hS

/--
[ons_decoratedSpinPolynomial_coeff_finsetExponent_of_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decoratedSpinPolynomial_coeff_finsetExponent_of_not_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)}
-- given
  (hS : S ∉ evenSubgraphs (ons_decGraph L)) :
-- imply
  MvPolynomial.coeff (ons_finsetExponent S) (ons_decoratedSpinPolynomial L a b) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinPolynomial_coeff_finsetExponent_of_not_even L a b S hS

/--
[ons_decFormalRoot_coeff_finsetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_finsetExponent_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {S : Finset (ons_DecEdge L)} :
-- imply
  MvPowerSeries.coeff (ons_finsetExponent S) (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = MvPowerSeries.coeff (ons_finsetExponent S) (ons_decoratedSpinPolynomial L a b : MvPowerSeries (ons_DecEdge L) ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_finsetExponent L a b S

/--
[ons_eq_finsetExponent_support_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_eq_finsetExponent_support_of_squarefree_eq
  [DecidableEq E]
  {m : E →₀ ℕ}
-- given
  (hm : ons_IsSquarefreeExponent m) :
-- imply
  m = ons_finsetExponent m.support := by
-- proof
  apply StatMech.Onsager.ons_eq_finsetExponent_support_of_squarefree m hm

/--
[ons_decoratedSpinPolynomial_coeff_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decoratedSpinPolynomial_coeff_eq_zero_of_not_squarefree_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {m : ons_DecEdge L →₀ ℕ}
-- given
  (hm : ¬ ons_IsSquarefreeExponent m) :
-- imply
  MvPowerSeries.coeff m (ons_decoratedSpinPolynomial L a b : MvPowerSeries (ons_DecEdge L) ℂ) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinPolynomial_coeff_eq_zero_of_not_squarefree L a b m hm

/--
[ons_decoratedFormalKacWardIdentity_of_nonsquarefree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean)
-/
@[path]
private lemma ons_decoratedFormalKacWardIdentity_of_nonsquarefree_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hnonsquare : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ), ¬ ons_IsSquarefreeExponent m → MvPowerSeries.coeff m (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
-- imply
  ons_decoratedFormalKacWardIdentity L := by
-- proof
  apply StatMech.Onsager.ons_decoratedFormalKacWardIdentity_of_nonsquarefree_zero L hnonsquare


-- created on 2026-10-23
