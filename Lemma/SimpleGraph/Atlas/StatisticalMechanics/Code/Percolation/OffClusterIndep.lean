import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.OffClusterIndep
open MeasureTheory Set SimpleGraph StatMech StatMech.Percolation


/--
[firstExitIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma firstExitIndex_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {D : Set V}
  [DecidablePred (· ∈ D)]
-- given
  (hb : b ∉ D) :
-- imply
  ∃ j, j ≤ p.length ∧ p.getVert j ∉ D ∧ ∀ i, i < j → p.getVert i ∈ D := by
-- proof
  apply StatMech.Percolation.firstExitIndex p D hb

/--
[take_support_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma take_support_sub_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {D : Set V}
  {j : ℕ}
-- given
  (hbefore : ∀ i, i < j → p.getVert i ∈ D) :
-- imply
  ∀ z ∈ (p.take j).support, z ∈ D ∨ z = p.getVert j := by
-- proof
  apply StatMech.Percolation.take_support_sub p D hbefore

/--
[exists_firstExit_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma exists_firstExit_induce_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {D T : Set V}
  [DecidablePred (· ∈ D)]
-- given
  (ha : a ∈ T)
  (hb : b ∉ D)
  (hDinT : ∀ i, p.getVert i ∈ D → p.getVert i ∈ T)
  (hstep : ∀ i, i < p.length → p.getVert i ∈ D → p.getVert (i + 1) ∈ T) :
-- imply
  ∃ (w : V) (hwT : w ∈ T), w ∉ D ∧ Nonempty ((G.induce T).Walk ⟨a, ha⟩ ⟨w, hwT⟩) := by
-- proof
  apply StatMech.Percolation.exists_firstExit_induce p D T ha hb hDinT hstep

/--
[adj_box_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma adj_box_step_eq
  {d : ℕ}
  {m : ℕ}
  {x z : Site d}
-- given
  (hx : x ∈ box d m)
  (hadj : (hypercubicLattice d).Adj x z) :
-- imply
  z ∈ box d (m + 1) := by
-- proof
  apply StatMech.Percolation.adj_box_step hx hadj

/--
[mem_boxFinsetOC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma mem_boxFinsetOC_eq
  {d : ℕ}
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ boxFinsetOC d n ↔ x ∈ box d n := by
-- proof
  apply StatMech.Percolation.mem_boxFinsetOC

/--
[extract_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma extract_box_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {C : Set (Site d)}
  {y v : Site d}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hyC : y ∉ C)
  (hvC : v ∉ C)
  (hybox : y ∈ box d n)
  (hvbox : v ∉ box d (n - 1))
  (hconn : ConnectedWithin d ω {z | z ∉ C} ⟨y, hyC⟩ ⟨v, hvC⟩) :
-- imply
  ∃ (z : Site d) (hz : z ∈ box d n \ C), z ∉ box d (n - 1) ∧ ConnectedWithin d ω (box d n \ C) ⟨y, hybox, hyC⟩ ⟨z, hz⟩ := by
-- proof
  apply StatMech.Percolation.extract_box ω C y v n hn hyC hvC hybox hvbox hconn

/--
[connWithinR_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma connWithinR_congr_eq
  {d : ℕ}
  {R : Set (Site d)}
  {a b : Site d}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (ha : a ∈ R)
  (hb : b ∈ R)
  (h : ∀ x ∈ R, ∀ z ∈ R, ω s(x, z) = ω' s(x, z)) :
-- imply
  ConnectedWithin d ω R ⟨a, ha⟩ ⟨b, hb⟩ ↔ ConnectedWithin d ω' R ⟨a, ha⟩ ⟨b, hb⟩ := by
-- proof
  apply StatMech.Percolation.connWithinR_congr R ha hb h

/--
[mem_boxOffCEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma mem_boxOffCEdges_eq
  {d : ℕ}
  {C : Set (Site d)}
  {n : ℕ}
  {x z : Site d}
-- given
  (hx : x ∈ box d n)
  (hxC : x ∉ C)
  (hz : z ∈ box d n)
  (hzC : z ∉ C) :
-- imply
  s(x, z) ∈ boxOffCEdges d C n := by
-- proof
  apply StatMech.Percolation.mem_boxOffCEdges hx hxC hz hzC

/--
[agree_boxOffC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma agree_boxOffC_eq
  {d : ℕ}
  {C : Set (Site d)}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x z : Site d}
-- given
  (hagree : ∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), ω e = ω' e)
  (hx : x ∈ box d n \ C)
  (hz : z ∈ box d n \ C) :
-- imply
  ω s(x, z) = ω' s(x, z) := by
-- proof
  apply StatMech.Percolation.agree_boxOffC hagree hx hz

/--
[offClusterBoxCrossing_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma offClusterBoxCrossing_congr_eq
  {d : ℕ}
  {C : Set (Site d)}
  {y : Site d}
  {n : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (hagree : ∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), ω e = ω' e) :
-- imply
  offClusterBoxCrossing d C y n ω ↔ offClusterBoxCrossing d C y n ω' := by
-- proof
  apply StatMech.Percolation.offClusterBoxCrossing_congr hagree

/--
[offClusterBoxCrossing_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma offClusterBoxCrossing_dependsOn_eq
  {d : ℕ}
  {C : Set (Site d)}
  {y : Site d}
  {n : ℕ} :
-- imply
  DependsOn ({ω | offClusterBoxCrossing d C y n ω}.indicator (fun _ => (1 : ℝ))) (boxOffCEdges d C n : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Percolation.offClusterBoxCrossing_dependsOn C y n

/--
[disjoint_boxOffC_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma disjoint_boxOffC_incident_eq
  {d : ℕ}
  {K S : Finset (Site d)}
  {n : ℕ} :
-- imply
  Disjoint (boxOffCEdges d (K : Set (Site d)) n) (incidentWithinFinset K S) := by
-- proof
  apply StatMech.Percolation.disjoint_boxOffC_incident K S n

/--
[boundaryEdge_notMem_boxOffC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma boundaryEdge_notMem_boxOffC_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {x y : Site d}
  {n : ℕ}
-- given
  (hxK : x ∈ K) :
-- imply
  s(x, y) ∉ boxOffCEdges d (K : Set (Site d)) n := by
-- proof
  apply StatMech.Percolation.boundaryEdge_notMem_boxOffC K x y n hxK

/--
[disjoint_boxOffC_incidentUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma disjoint_boxOffC_incidentUnion_eq
  {d : ℕ}
  {K S : Finset (Site d)}
  {x y : Site d}
  {n : ℕ}
-- given
  (hxK : x ∈ K) :
-- imply
  Disjoint (incidentWithinFinset K S ∪ {s(x, y)}) (boxOffCEdges d (K : Set (Site d)) n) := by
-- proof
  apply StatMech.Percolation.disjoint_boxOffC_incidentUnion K S x y n hxK

/--
[dependsOn_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma dependsOn_inter_eq
  {d : ℕ}
  {A B : Set (ConfigSpace E)}
  {T U : Set E}
-- given
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) T)
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) U) :
-- imply
  DependsOn ((A ∩ B).indicator (fun _ => (1 : ℝ))) (T ∪ U) := by
-- proof
  apply StatMech.Percolation.dependsOn_inter hA hB

/--
[offCluster_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma offCluster_factor_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {K : Finset (Site d)}
  {x y : Site d}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hxK : x ∈ K) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω}) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω} := by
-- proof
  apply StatMech.Percolation.offCluster_factor p hp S hoS K x y n hxK

/--
[offClusterBox_subset_crossingFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma offClusterBox_subset_crossingFrom_eq
  {d : ℕ}
  {C : Set (Site d)}
  {y : Site d}
  {n : ℕ} :
-- imply
  {ω | offClusterBoxCrossing d C y n ω} ⊆ crossingEventFrom d y n := by
-- proof
  apply StatMech.Percolation.offClusterBox_subset_crossingFrom C y n

/--
[offClusterBox_crossProb_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma offClusterBox_crossProb_le_eq
  {d : ℕ}
  {C : Set (Site d)}
  {y : Site d}
  {L m n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hy : y ∈ box d L)
  (hmLn : m + L ≤ n)
  (hm : 1 ≤ m) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real {ω | offClusterBoxCrossing d C y n ω} ≤ crossProb d p hp m := by
-- proof
  apply StatMech.Percolation.offClusterBox_crossProb_le p hp C y hy hmLn hm

/--
[crossingEvent_lastExit_boxsubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean)
-/
@[path]
private lemma crossingEvent_lastExit_boxsubset_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {n : ℕ}
-- given
  (hoS : origin d ∈ (S : Set (Site d)))
  (hn : 1 ≤ n)
  (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
-- imply
  crossingEvent d n ⊆ ⋃ (K : Finset (Site d)), ⋃ (x : Site d), ⋃ (y : Site d), (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω} ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω}) := by
-- proof
  apply StatMech.Percolation.crossingEvent_lastExit_boxsubset S hoS n hn hSbox


-- created on 2026-10-23
