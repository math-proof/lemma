import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
open MeasureTheory Function Set SimpleGraph Filter StatMech StatMech.Percolation


/--
[isPivotal_box_congr_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma isPivotal_box_congr_erase_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (Site d)}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∀ e' ∈ (((boxEdgeFinset d n).erase e : Finset (Sym2 (Site d))) : Set (Sym2 (Site d))), ω e' = ω' e') :
-- imply
  IsPivotal e (boxCrossingEvent d n) ω ↔ IsPivotal e (boxCrossingEvent d n) ω' := by
-- proof
  apply StatMech.Percolation.isPivotal_box_congr_erase n e h

/--
[pivotalEvent_dependsOn_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma pivotalEvent_dependsOn_erase_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (Site d)} :
-- imply
  DependsOn ((pivotalEvent e (boxCrossingEvent d n)).indicator (fun _ => (1 : ℝ))) (((boxEdgeFinset d n).erase e : Finset (Sym2 (Site d))) : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Percolation.pivotalEvent_dependsOn_erase n e

/--
[coord_false_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma coord_false_dependsOn_eq
  {d : ℕ}
  {e : E} :
-- imply
  DependsOn (({ω : ConfigSpace E | ω e = false}).indicator (fun _ => (1 : ℝ))) ({e} : Set E) := by
-- proof
  apply StatMech.Percolation.coord_false_dependsOn e

/--
[coord_false_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma coord_false_prob_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real {ω | ω e = false} = 1 - (p : ℝ) := by
-- proof
  apply StatMech.Percolation.coord_false_prob p hp e

/--
[pivotalProb_closed_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma pivotalProb_closed_factor_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent e (boxCrossingEvent d n) ∩ {ω | ω e = false}) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent e (boxCrossingEvent d n)) * (1 - (p : ℝ)) := by
-- proof
  apply StatMech.Percolation.pivotalProb_closed_factor p hp n e

/--
[surfaceSet_subset_innerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma surfaceSet_subset_innerBox_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (surfaceSet d n ω : Set (Site d)) ⊆ box d (n - 1) := by
-- proof
  apply StatMech.Percolation.surfaceSet_subset_innerBox n ω

/--
[connectedWithin_mono_set'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma connectedWithin_mono_set'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S T : Set (Site d)}
  {x y : S}
-- given
  (hST : S ⊆ T)
  (h : ConnectedWithin d ω S x y) :
-- imply
  ConnectedWithin d ω T ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
-- proof
  apply StatMech.Percolation.connectedWithin_mono_set' ω hST h

/--
[connectedWithin_box_mono_omega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma connectedWithin_box_mono_omega_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x y : ↥(box d n)}
-- given
  (hle : ω ≤ ω')
  (h : ConnectedWithin d ω (box d n) x y) :
-- imply
  ConnectedWithin d ω' (box d n) x y := by
-- proof
  apply StatMech.Percolation.connectedWithin_box_mono_omega hle h

/--
[origin_mem_box'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma origin_mem_box'_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  origin d ∈ box d n := by
-- proof
  apply StatMech.Percolation.origin_mem_box' n

/--
[surface_boundary_edge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma surface_boundary_edge_closed_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (hS : surfaceSet d n ω = S)
  (hadj : (hypercubicLattice d).Adj x y)
  (hxS : x ∈ S)
  (hybox : y ∈ box d n)
  (hyS : y ∉ S) :
-- imply
  ω s(x, y) = false := by
-- proof
  apply StatMech.Percolation.surface_boundary_edge_closed hS hadj hxS hybox hyS

/--
[mem_boxCrossingEvent_iff_connBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma mem_boxCrossingEvent_iff_connBdry_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ boxCrossingEvent d n ↔ connBdry d n ω (origin d) := by
-- proof
  apply StatMech.Percolation.mem_boxCrossingEvent_iff_connBdry n ω

/--
[boundary_edge_isPivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma boundary_edge_isPivotal_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (hS : surfaceSet d n ω = S)
  (h0S : origin d ∈ S)
  (hadj : (hypercubicLattice d).Adj x y)
  (hxS : x ∈ S)
  (hybox : y ∈ box d n)
  (hyS : y ∉ S)
  (hconn : ConnectedWithin d ω (S : Set (Site d)) ⟨origin d, by exact_mod_cast h0S⟩ ⟨x, by exact_mod_cast hxS⟩) :
-- imply
  IsPivotal (s(x, y) : Sym2 (Site d)) (boxCrossingEvent d n) ω := by
-- proof
  apply StatMech.Percolation.boundary_edge_isPivotal hS h0S hadj hxS hybox hyS hconn

/--
[boundaryEdges_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma boundaryEdges_adj_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (he : e ∈ boundaryEdges d S) :
-- imply
  (hypercubicLattice d).Adj e.1 e.2 := by
-- proof
  apply StatMech.Percolation.boundaryEdges_adj he

/--
[boundaryEdge_mem_boxEdgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma boundaryEdge_mem_boxEdgeFinset_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (hSinner : (S : Set (Site d)) ⊆ box d (n - 1))
  (hn : 1 ≤ n)
  (he : e ∈ boundaryEdges d S) :
-- imply
  s(e.1, e.2) ∈ boxEdgeFinset d n := by
-- proof
  apply StatMech.Percolation.boundaryEdge_mem_boxEdgeFinset hSinner hn he

/--
[boundaryEdges_sym2_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma boundaryEdges_sym2_injOn_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  Set.InjOn (fun e : Site d × Site d => (s(e.1, e.2) : Sym2 (Site d))) (boundaryEdges d S : Set (Site d × Site d)) := by
-- proof
  apply StatMech.Percolation.boundaryEdges_sym2_injOn S

/--
[sum_le_sum_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma sum_le_sum_injOn_eq
  {d : ℕ}
  [DecidableEq β]
  {s : Finset α}
  {t : Finset β}
  {φ : α → β}
  {g : α → ℝ}
  {f : β → ℝ}
-- given
  (hmap : ∀ a ∈ s, φ a ∈ t)
  (hinj : Set.InjOn φ s)
  (hle : ∀ a ∈ s, g a ≤ f (φ a))
  (hf : ∀ b ∈ t, 0 ≤ f b) :
-- imply
  ∑ a ∈ s, g a ≤ ∑ b ∈ t, f b := by
-- proof
  apply StatMech.Percolation.sum_le_sum_injOn s t φ g f hmap hinj hle hf

/--
[withinConn_surf_subset_pivotalClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma withinConn_surf_subset_pivotalClosed_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (h0S : origin d ∈ S)
  (hSinner : (S : Set (Site d)) ⊆ box d (n - 1))
  (hn : 1 ≤ n)
  (he : e ∈ boundaryEdges d S) :
-- imply
  withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ surfaceEvent d n S ⊆ (pivotalEvent (s(e.1, e.2)) (boxCrossingEvent d n) ∩ {ω | ω s(e.1, e.2) = false}) ∩ surfaceEvent d n S := by
-- proof
  apply StatMech.Percolation.withinConn_surf_subset_pivotalClosed h0S hSinner hn he

/--
[perSurface_boundary_le_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma perSurface_boundary_le_pivotal_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0S : origin d ∈ S)
  (hSinner : (S : Set (Site d)) ⊆ box d (n - 1))
  (hn : 1 ≤ n) :
-- imply
  ∑ e' ∈ boundaryEdges d S, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S) ≤ ∑ edge ∈ boxEdgeFinset d n, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real ((pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false}) ∩ surfaceEvent d n S) := by
-- proof
  apply StatMech.Percolation.perSurface_boundary_le_pivotal p hp h0S hSinner hn

/--
[perSurface_boundary_eq_phi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma perSurface_boundary_eq_phi_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hp0 : 0 < (p : ℝ))
  (h0S : origin d ∈ S) :
-- imply
  ∑ e' ∈ boundaryEdges d S, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S) = (1 / (p : ℝ)) * (phi d p hp S * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S)) := by
-- proof
  apply StatMech.Percolation.perSurface_boundary_eq_phi p hp hp0 h0S

/--
[measurableSet_pivotalClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma measurableSet_pivotalClosed_eq
  {d : ℕ}
  {n : ℕ}
  {edge : Sym2 (Site d)} :
-- imply
  MeasurableSet (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false}) := by
-- proof
  apply StatMech.Percolation.measurableSet_pivotalClosed n edge

/--
[sum_inter_surface_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma sum_inter_surface_le_eq
  {d : ℕ}
  {n : ℕ}
  {E : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hE : MeasurableSet E) :
-- imply
  ∑ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∈ S), (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (E ∩ surfaceEvent d n S) ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real E := by
-- proof
  apply StatMech.Percolation.sum_inter_surface_le p hp n hE

/--
[biUnion_surface_not_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma biUnion_surface_not_origin_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (⋃ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∉ S), surfaceEvent d n S) = boxCrossingEvent d n := by
-- proof
  apply StatMech.Percolation.biUnion_surface_not_origin n

/--
[sum_surfaceProb_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma sum_surfaceProb_origin_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  ∑ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∈ S), (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) = 1 - boxCrossProb d p hp n := by
-- proof
  apply StatMech.Percolation.sum_surfaceProb_origin p hp n

/--
[sum_pivotalClosed_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma sum_pivotalClosed_eq_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  ∑ edge ∈ boxEdgeFinset d n, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false}) = (1 - (p : ℝ)) * deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ) := by
-- proof
  apply StatMech.Percolation.sum_pivotalClosed_eq p hp n

/--
[dct_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma dct_differential_inequality_eq
  {d : ℕ}
  {n : ℕ}
  {m : ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hn : 1 ≤ n)
  (hp0 : 0 < (p : ℝ))
  (hp1 : (p : ℝ) < 1)
  (hm : ∀ S : Finset (Site d), origin d ∈ S → m ≤ phi d p hp S) :
-- imply
  deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ) ≥ (1 / ((p : ℝ) * (1 - (p : ℝ)))) * m * (1 - boxCrossProb d p hp n) := by
-- proof
  apply StatMech.Percolation.dct_differential_inequality p hp n hn hp0 hp1 m hm

/--
[firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma firstExit_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {S : Set V}
  [DecidablePred (· ∈ S)]
-- given
  (ha : a ∈ S)
  (hb : b ∉ S) :
-- imply
  ∃ (x y : V) (hx : x ∈ S) (_hy : y ∉ S) (_hadj : G.Adj x y), Nonempty ((G.induce S).Walk ⟨a, ha⟩ ⟨x, hx⟩) := by
-- proof
  apply StatMech.Percolation.firstExit p S ha hb

/--
[crossingEvent_eq_boxCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma crossingEvent_eq_boxCrossingEvent_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  crossingEvent d n = boxCrossingEvent d n := by
-- proof
  apply StatMech.Percolation.crossingEvent_eq_boxCrossingEvent n hn

/--
[crossProb_eq_boxCrossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma crossProb_eq_boxCrossProb_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hn : 1 ≤ n) :
-- imply
  crossProb d p hp n = boxCrossProb d p hp n := by
-- proof
  apply StatMech.Percolation.crossProb_eq_boxCrossProb p hp n hn

/--
[crossProbReal_eq_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma crossProbReal_eq_prob_eq
  {d : ℕ}
  {n : ℕ}
  {t : ℝ}
-- given
  (ht0 : 0 ≤ t)
  (ht1 : t ≤ 1) :
-- imply
  crossProbReal d (n + 1) t = prob t ((boxEdgeFinset d (n + 1)).restrict '' (boxCrossingEvent d (n + 1))) := by
-- proof
  apply StatMech.Percolation.crossProbReal_eq_prob n ht0 ht1

/--
[continuousOn_crossProbReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma continuousOn_crossProbReal_eq
  {d : ℕ}
  {n : ℕ}
  {a b : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : b ≤ 1) :
-- imply
  ContinuousOn (crossProbReal d (n + 1)) (Icc a b) := by
-- proof
  apply StatMech.Percolation.continuousOn_crossProbReal n ha hb

/--
[hasDerivAt_crossProbReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma hasDerivAt_crossProbReal_eq
  {d : ℕ}
  {n : ℕ}
  {t : ℝ}
-- given
  (ht0 : 0 < t)
  (ht1 : t < 1) :
-- imply
  HasDerivAt (crossProbReal d (n + 1)) (deriv (crossPoly d n) t) t := by
-- proof
  apply StatMech.Percolation.hasDerivAt_crossProbReal n ht0 ht1

/--
[phi_ge_one_of_gt_tildePc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma phi_ge_one_of_gt_tildePc_eq
  {d : ℕ}
  {p : ℝ≥0}
  {S : Finset (Site d)}
-- given
  (hp : p ≤ 1)
  (hgt : tildePc d < p)
  (h0S : origin d ∈ S) :
-- imply
  1 ≤ phi d p hp S := by
-- proof
  apply StatMech.Percolation.phi_ge_one_of_gt_tildePc hp hgt S h0S

/--
[dct_diffineq_crossProbReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma dct_diffineq_crossProbReal_eq
  {d : ℕ}
  {q : ℝ≥0}
  {n : ℕ}
  {t : ℝ}
-- given
  (hq1 : (q : ℝ) < 1)
  (htpc0 : 0 < (tildePc d : ℝ))
  (ht : t ∈ Ioo (tildePc d : ℝ) (q : ℝ)) :
-- imply
  deriv (crossPoly d n) t ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t) := by
-- proof
  apply StatMech.Percolation.dct_diffineq_crossProbReal hq1 htpc0 n ht

/--
[theta_ge_meanField_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean)
-/
@[path]
private lemma theta_ge_meanField_unconditional_eq
  {d : ℕ}
-- given
  (q : ℝ≥0)
  (hq : q ≤ 1)
  (htpc0 : 0 < (tildePc d : ℝ))
  (hgt : tildePc d < q)
  (hq1 : (q : ℝ) < 1) :
-- imply
  theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ))) := by
-- proof
  apply StatMech.Percolation.theta_ge_meanField_unconditional q hq htpc0 hgt hq1


-- created on 2026-10-23
