import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DctSurfacePartition.Part4
open MeasureTheory Function Set SimpleGraph StatMech StatMech.Percolation


/--
[mem_pivotalEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma mem_pivotalEvent_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ pivotalEvent e A ↔ IsPivotal e A ω := by
-- proof
  apply StatMech.Percolation.mem_pivotalEvent

/--
[pivotalEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma pivotalEvent_dependsOn_eq
  {d : ℕ}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
-- imply
  DependsOn ((pivotalEvent e A).indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Percolation.pivotalEvent_dependsOn A F e hA

/--
[restrict_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma restrict_setOpen_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (he : e ∈ F) :
-- imply
  F.restrict (setOpen e ω) = setOpen (⟨e, he⟩ : ↥F) (F.restrict ω) := by
-- proof
  apply StatMech.Percolation.restrict_setOpen F e he ω

/--
[restrict_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma restrict_setClosed_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (he : e ∈ F) :
-- imply
  F.restrict (setClosed e ω) = setClosed (⟨e, he⟩ : ↥F) (F.restrict ω) := by
-- proof
  apply StatMech.Percolation.restrict_setClosed F e he ω

/--
[restrict_image_pivotalEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma restrict_image_pivotalEvent_eq
  {d : ℕ}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (he : e ∈ F)
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
-- imply
  F.restrict '' (pivotalEvent e A) = {η : ConfigSpace ↥F | IsPivotal (⟨e, he⟩ : ↥F) (F.restrict '' A) η} := by
-- proof
  apply StatMech.Percolation.restrict_image_pivotalEvent A F e he hA

/--
[pivotalProb_eq_realPivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma pivotalProb_eq_realPivotal_eq
  {d : ℕ}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (he : e ∈ F)
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set (Sym2 (Site d)))) :
-- imply
  pivotalProb (p : ℝ) (F.restrict '' A) (⟨e, he⟩ : ↥F) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent e A) := by
-- proof
  apply StatMech.Percolation.pivotalProb_eq_realPivotal p hp A F e he hA

/--
[deriv_boxCrossProb_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma deriv_boxCrossProb_inf_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ) = ∑ e : ↥(boxEdgeFinset d n), (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent (↑e : Sym2 (Site d)) (boxCrossingEvent d n)) := by
-- proof
  apply StatMech.Percolation.deriv_boxCrossProb_inf p hp n

/--
[mem_surfaceSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma mem_surfaceSet_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  x ∈ surfaceSet d n ω ↔ x ∈ box d n ∧ ¬ connBdry d n ω x := by
-- proof
  apply StatMech.Percolation.mem_surfaceSet

/--
[surfaceSet_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma surfaceSet_subset_box_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  surfaceSet d n ω ⊆ boxFinset d n := by
-- proof
  apply StatMech.Percolation.surfaceSet_subset_box n ω

/--
[surfaceSet_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma surfaceSet_congr_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e) :
-- imply
  surfaceSet d n ω = surfaceSet d n ω' := by
-- proof
  apply StatMech.Percolation.surfaceSet_congr n h

/--
[surfaceEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma surfaceEvent_dependsOn_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)} :
-- imply
  DependsOn ((surfaceEvent d n S).indicator (fun _ => (1 : ℝ))) ((boxEdgeFinset d n : Set (Sym2 (Site d)))) := by
-- proof
  apply StatMech.Percolation.surfaceEvent_dependsOn n S

/--
[measurableSet_surfaceEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma measurableSet_surfaceEvent_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)} :
-- imply
  MeasurableSet (surfaceEvent d n S) := by
-- proof
  apply StatMech.Percolation.measurableSet_surfaceEvent n S

/--
[sum_surfaceProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma sum_surfaceProb_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  ∑ S ∈ (boxFinset d n).powerset, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) = 1 := by
-- proof
  apply StatMech.Percolation.sum_surfaceProb p hp n

/--
[disjoint_boxEdgesOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma disjoint_boxEdgesOutside_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)} :
-- imply
  Disjoint (edgesWithinFinset S) (boxEdgesOutside d n S) := by
-- proof
  apply StatMech.Percolation.disjoint_boxEdgesOutside n S

/--
[pair_mem_boxEdgesOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma pair_mem_boxEdgesOutside_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
  {a z : Site d}
-- given
  (ha : a ∈ box d n)
  (hz : z ∈ box d n)
  (hor : a ∉ S ∨ z ∉ S) :
-- imply
  s(a, z) ∈ boxEdgesOutside d n S := by
-- proof
  apply StatMech.Percolation.pair_mem_boxEdgesOutside ha hz hor

/--
[walk_vertex_connBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma walk_vertex_connBdry_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a y : ↥(box d n)}
  {w : (openSubgraphInduce d ω (box d n)).Walk a y}
  {v : ↥(box d n)}
-- given
  (hy : (y : Site d) ∈ vertexBoundary d n)
  (hv : v ∈ w.support) :
-- imply
  connBdry d n ω (v : Site d) := by
-- proof
  apply StatMech.Percolation.walk_vertex_connBdry hy w v hv

/--
[walk_transfer_avoidS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma walk_transfer_avoidS_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {a b : ↥(box d n)}
  {w : (openSubgraphInduce d ω (box d n)).Walk a b}
-- given
  (hagree : ∀ x z : Site d, x ∈ box d n → z ∈ box d n → (x ∉ S ∨ z ∉ S) → ω s(x, z) = ω' s(x, z))
  (hsupp : ∀ v ∈ w.support, (v : Site d) ∉ S) :
-- imply
  Nonempty ((openSubgraphInduce d ω' (box d n)).Walk a b) := by
-- proof
  apply StatMech.Percolation.walk_transfer_avoidS hagree w hsupp

/--
[connBdry_of_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma connBdry_of_mem_boundary_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy : y ∈ box d n)
  (hyb : y ∈ vertexBoundary d n) :
-- imply
  connBdry d n ω y := by
-- proof
  apply StatMech.Percolation.connBdry_of_mem_boundary hy hyb

/--
[connBdry_of_open_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma connBdry_of_open_edge_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
-- given
  (hu : u ∈ box d n)
  (hw : w ∈ box d n)
  (hopen : IsOpenEdge d ω u w)
  (hcbw : connBdry d n ω w) :
-- imply
  connBdry d n ω u := by
-- proof
  apply StatMech.Percolation.connBdry_of_open_edge hu hw hopen hcbw

/--
[connBdry_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma connBdry_transfer_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (hS : surfaceSet d n ω = S)
  (hagree : ∀ a z : Site d, a ∈ box d n → z ∈ box d n → (a ∉ S ∨ z ∉ S) → ω s(a, z) = ω' s(a, z))
  (hxbox : x ∈ box d n) :
-- imply
  connBdry d n ω x ↔ connBdry d n ω' x := by
-- proof
  apply StatMech.Percolation.connBdry_transfer hS hagree hxbox

/--
[surfaceSet_congr_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma surfaceSet_congr_outside_eq
  {d : ℕ}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
-- given
  (hS : surfaceSet d n ω = S)
  (h : ∀ e ∈ (boxEdgesOutside d n S : Set (Sym2 (Site d))), ω e = ω' e) :
-- imply
  surfaceSet d n ω' = S := by
-- proof
  apply StatMech.Percolation.surfaceSet_congr_outside n hS h

/--
[surfaceEvent_dependsOn_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma surfaceEvent_dependsOn_outside_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)} :
-- imply
  DependsOn ((surfaceEvent d n S).indicator (fun _ => (1 : ℝ))) ((boxEdgesOutside d n S : Set (Sym2 (Site d)))) := by
-- proof
  apply StatMech.Percolation.surfaceEvent_dependsOn_outside n S

/--
[surface_withinConn_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean)
-/
@[path]
private lemma surface_withinConn_indep_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
  {o x : Site d}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) o x ∩ surfaceEvent d n S) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) o x) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) := by
-- proof
  apply StatMech.Percolation.surface_withinConn_indep p hp n S o x


-- created on 2026-10-23
