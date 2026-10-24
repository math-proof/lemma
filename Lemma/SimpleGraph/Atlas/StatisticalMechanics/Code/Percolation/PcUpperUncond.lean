import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.PcUpperUncond
open MeasureTheory Filter Topology Finset Set SimpleGraph StatMech StatMech.Percolation


/--
[cylinder_all_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma cylinder_all_closed_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) ((F : Set (Sym2 (Site d))).pi (fun _ => ({false} : Set Bool))) = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ F.card := by
-- proof
  apply StatMech.Percolation.cylinder_all_closed p hp F

/--
[sharedPrimalEdge_right'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma sharedPrimalEdge_right'_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a + 1, b] = s(![a + 1, b], ![a + 1, b + 1]) := by
-- proof
  apply StatMech.Percolation.sharedPrimalEdge_right' a b

/--
[sharedPrimalEdge_left'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma sharedPrimalEdge_left'_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a - 1, b] = s(![a, b], ![a, b + 1]) := by
-- proof
  apply StatMech.Percolation.sharedPrimalEdge_left' a b

/--
[sharedPrimalEdge_top'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma sharedPrimalEdge_top'_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a, b + 1] = s(![a, b + 1], ![a + 1, b + 1]) := by
-- proof
  apply StatMech.Percolation.sharedPrimalEdge_top' a b

/--
[sharedPrimalEdge_bottom'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma sharedPrimalEdge_bottom'_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a, b - 1] = s(![a, b], ![a + 1, b]) := by
-- proof
  apply StatMech.Percolation.sharedPrimalEdge_bottom' a b

/--
[face_adj_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma face_adj_dir_eq
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  (g = ![f 0 + 1, f 1]) ∨ (g = ![f 0 - 1, f 1]) ∨ (g = ![f 0, f 1 + 1]) ∨ (g = ![f 0, f 1 - 1]) := by
-- proof
  apply StatMech.Percolation.face_adj_dir h

/--
[sharedPrimalEdge_uncrossInj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma sharedPrimalEdge_uncrossInj_eq
  {f g f' g' : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g)
  (h' : (hypercubicLattice 2).Adj f' g')
  (heq : sharedPrimalEdge f g = sharedPrimalEdge f' g') :
-- imply
  s(f, g) = s(f', g') := by
-- proof
  apply StatMech.Percolation.sharedPrimalEdge_uncrossInj h h' heq

/--
[closedCircuitEvent_eq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma closedCircuitEvent_eq_pi_eq
  {u v : Site 2}
  {c : (hypercubicLattice 2).Walk u v} :
-- imply
  closedCircuitEvent c = ((primalEdgeFinset c : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))).pi (fun _ => ({false} : Set Bool)) := by
-- proof
  apply StatMech.Percolation.closedCircuitEvent_eq_pi c

/--
[measure_closedCircuitEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma measure_closedCircuitEvent_eq
  {u v : Site 2}
  {c : (hypercubicLattice 2).Walk u v}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedCircuitEvent c) = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ (primalEdgeFinset c).card := by
-- proof
  apply StatMech.Percolation.measure_closedCircuitEvent p hp c

/--
[primalEdgeList_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma primalEdgeList_nodup_eq
  {u : Site 2}
  {c : (hypercubicLattice 2).Walk u u}
-- given
  (hc : c.IsCycle) :
-- imply
  (c.darts.map (fun D => sharedPrimalEdge D.fst D.snd)).Nodup := by
-- proof
  apply StatMech.Percolation.primalEdgeList_nodup c hc

/--
[primalEdgeFinset_card_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma primalEdgeFinset_card_cycle_eq
  {u : Site 2}
  {c : (hypercubicLattice 2).Walk u u}
-- given
  (hc : c.IsCycle) :
-- imply
  (primalEdgeFinset c).card = c.length := by
-- proof
  apply StatMech.Percolation.primalEdgeFinset_card_cycle c hc

/--
[measure_closedCircuitEvent_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma measure_closedCircuitEvent_cycle_eq
  {u : Site 2}
  {c : (hypercubicLattice 2).Walk u u}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hc : c.IsCycle) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedCircuitEvent c) = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ c.length := by
-- proof
  apply StatMech.Percolation.measure_closedCircuitEvent_cycle p hp c hc

/--
[anchorFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma anchorFinset_card_eq
  {ℓ : ℕ} :
-- imply
  (anchorFinset ℓ).card ≤ 2 * ℓ := by
-- proof
  apply StatMech.Percolation.anchorFinset_card ℓ

/--
[cyclesAtLen_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma cyclesAtLen_card_eq
  {ℓ : ℕ} :
-- imply
  (cyclesAtLen ℓ).card ≤ 2 * ℓ * 4 ^ ℓ := by
-- proof
  apply StatMech.Percolation.cyclesAtLen_card ℓ

/--
[measure_cyclesAtLen_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma measure_cyclesAtLen_le_eq
  {ℓ : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2) ≤ (2 * ℓ * 4 ^ ℓ : ℕ) * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ := by
-- proof
  apply StatMech.Percolation.measure_cyclesAtLen_le p hp ℓ

/--
[pcSummandTwo_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma pcSummandTwo_eq_eq
  {p : ℝ}
  {ℓ : ℕ} :
-- imply
  pcSummandTwo p ℓ = 2 * ((ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ) := by
-- proof
  apply StatMech.Percolation.pcSummandTwo_eq p ℓ

/--
[pcSummandTwo_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma pcSummandTwo_nonneg_eq
  {p : ℝ}
  {ℓ : ℕ}
-- given
  (hp : p ≤ 1) :
-- imply
  0 ≤ pcSummandTwo p ℓ := by
-- proof
  apply StatMech.Percolation.pcSummandTwo_nonneg hp ℓ

/--
[summable_pcSummandTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma summable_pcSummandTwo_eq
  {p : ℝ}
-- given
  (hx : ‖pcRatio p‖ < 1) :
-- imply
  Summable (pcSummandTwo p) := by
-- proof
  apply StatMech.Percolation.summable_pcSummandTwo p hx

/--
[tsum_pcSummandTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma tsum_pcSummandTwo_eq
  {p : ℝ} :
-- imply
  ∑' ℓ : ℕ, pcSummandTwo p ℓ = 2 * pcUpperBound p := by
-- proof
  apply StatMech.Percolation.tsum_pcSummandTwo p

/--
[ennSummand_eq_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma ennSummand_eq_ofReal_eq
  {ℓ : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  ((2 * ℓ * 4 ^ ℓ : ℕ) : ℝ≥0∞) * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ = ENNReal.ofReal (pcSummandTwo (p : ℝ) ℓ) := by
-- proof
  apply StatMech.Percolation.ennSummand_eq_ofReal p hp ℓ

/--
[mapLe_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma mapLe_length_eq
  {S : Set (Site 2)}
  {u : Site 2}
  {c : (faceBoundaryGraph S).Walk u u} :
-- imply
  (c.mapLe (faceBoundaryGraph_le S)).length = c.length := by
-- proof
  apply StatMech.Percolation.mapLe_length S c

/--
[mapLe_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma mapLe_edges_eq
  {S : Set (Site 2)}
  {u : Site 2}
  {c : (faceBoundaryGraph S).Walk u u} :
-- imply
  (c.mapLe (faceBoundaryGraph_le S)).edges = c.edges := by
-- proof
  apply StatMech.Percolation.mapLe_edges S c

/--
[mapLe_dart_faceAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma mapLe_dart_faceAdj_eq
  {S : Set (Site 2)}
  {u : Site 2}
  {c : (faceBoundaryGraph S).Walk u u}
  {D : (hypercubicLattice 2).Dart}
-- given
  (hD : D ∈ (c.mapLe (faceBoundaryGraph_le S)).darts) :
-- imply
  (faceBoundaryGraph S).Adj D.fst D.snd := by
-- proof
  apply StatMech.Percolation.mapLe_dart_faceAdj S c D hD

/--
[sharedPrimalEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma sharedPrimalEdge_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {f g : Site 2}
-- given
  (h : (faceBoundaryGraph (cluster 2 ω o)).Adj f g) :
-- imply
  ω (sharedPrimalEdge f g) = false := by
-- proof
  apply StatMech.Percolation.sharedPrimalEdge_isClosed o h

/--
[percolationEventCompl_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma percolationEventCompl_subset_eq
-- given
  (henc : PcAnchoredEnclosure) :
-- imply
  (percolationEvent 2)ᶜ ⊆ ⋃ ℓ : ℕ, ⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2 := by
-- proof
  apply StatMech.Percolation.percolationEventCompl_subset henc

/--
[measure_compl_percolationEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma measure_compl_percolationEvent_le_eq
-- given
  (henc : PcAnchoredEnclosure)
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hsum : ‖pcRatio (p : ℝ)‖ < 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) ((percolationEvent 2)ᶜ) ≤ ENNReal.ofReal (2 * pcUpperBound (p : ℝ)) := by
-- proof
  apply StatMech.Percolation.measure_compl_percolationEvent_le henc p hp hsum

/--
[one_sub_theta_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma one_sub_theta_le_eq
-- given
  (henc : PcAnchoredEnclosure)
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hsum : ‖pcRatio (p : ℝ)‖ < 1) :
-- imply
  1 - theta 2 p hp ≤ 2 * pcUpperBound (p : ℝ) := by
-- proof
  apply StatMech.Percolation.one_sub_theta_le henc p hp hsum

/--
[pc_lt_one_of_enclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean)
-/
@[path]
private lemma pc_lt_one_of_enclosure_eq
-- given
  (henc : PcAnchoredEnclosure) :
-- imply
  pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pc_lt_one_of_enclosure henc


-- created on 2026-10-23
