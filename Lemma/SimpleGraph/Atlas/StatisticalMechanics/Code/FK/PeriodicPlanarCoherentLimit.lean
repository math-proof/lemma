import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit
open Finset Set SimpleGraph MeasureTheory Filter Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.finite_subset_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma finite_subset_orbitBox_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {S : Finset V} :
-- imply
  ∃ n, ∀ v ∈ S, v ∈ P.orbitBox n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finite_subset_orbitBox P S

/--
[PeriodicGraph.exists_buffer_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma exists_buffer_radius_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  ∃ m, n < m ∧ ∀ v ∈ P.orbitBox n, ∀ w, P.graph.Adj v w → w ∈ P.orbitBox m := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_buffer_radius P n

/--
[PeriodicGraph.lt_nextBufferedRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma lt_nextBufferedRadius_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  n < P.nextBufferedRadius n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.lt_nextBufferedRadius P n

/--
[PeriodicGraph.neighbor_mem_nextBufferedRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma neighbor_mem_nextBufferedRadius_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {v w : V}
-- given
  (hv : v ∈ P.orbitBox n)
  (hvw : P.graph.Adj v w) :
-- imply
  w ∈ P.orbitBox (P.nextBufferedRadius n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.neighbor_mem_nextBufferedRadius P n hv hvw

/--
[PeriodicGraph.bufferedRadius_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedRadius_zero_eq
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  P.bufferedRadius 0 = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRadius_zero P

/--
[PeriodicGraph.bufferedRadius_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedRadius_succ_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  P.bufferedRadius (n + 1) = P.nextBufferedRadius (P.bufferedRadius n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRadius_succ P n

/--
[PeriodicGraph.bufferedRadius_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedRadius_strictMono_eq
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  StrictMono P.bufferedRadius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRadius_strictMono P

/--
[PeriodicGraph.id_le_bufferedRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma id_le_bufferedRadius_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  n ≤ P.bufferedRadius n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.id_le_bufferedRadius P n

/--
[PeriodicGraph.mem_bufferedBox_of_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma mem_bufferedBox_of_eventually_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {v : V} :
-- imply
  ∃ n, v ∈ P.orbitBox (P.bufferedRadius n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_bufferedBox_of_eventually P v

/--
[PeriodicGraph.bufferedVertexInclLE_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedVertexInclLE_val_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n m : ℕ}
  {v : P.BufferedVertex n}
-- given
  (hnm : n ≤ m) :
-- imply
  (P.bufferedVertexInclLE hnm v : V) = v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedVertexInclLE_val P hnm v

/--
[PeriodicGraph.bufferedAdjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedAdjMatch_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  ocd_AdjMatch (P.bufferedGraph n) (P.bufferedGraph (n + 1)) (P.bufferedVertexIncl n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedAdjMatch P n

/--
[PeriodicGraph.neighbor_mem_buffered_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma neighbor_mem_buffered_succ_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {v w : V}
-- given
  (hv : v ∈ P.orbitBox (P.bufferedRadius n))
  (hvw : P.graph.Adj v w) :
-- imply
  w ∈ P.orbitBox (P.bufferedRadius (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.neighbor_mem_buffered_succ P n hv hvw

/--
[PeriodicGraph.not_bufferedBoundary_incl_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma not_bufferedBoundary_incl_succ_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {v : P.BufferedVertex n} :
-- imply
  ¬ P.bufferedBoundary (n + 1) (P.bufferedVertexIncl n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.not_bufferedBoundary_incl_succ P n v

/--
[PeriodicGraph.bufferedBoundary_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedBoundary_of_outsideGraph_adj_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {psi : ConfigSpace (Sym2 (P.BufferedVertex (n + 1)))}
  {x : P.BufferedVertex n}
  {z : P.BufferedVertex (n + 1)}
-- given
  (h : (ocd_outsideGraph (P.bufferedGraph (n + 1)) (P.bufferedVertexIncl n) (P.bufferedBoundary (n + 1)) psi).Adj (P.bufferedVertexIncl n x) z) :
-- imply
  P.bufferedBoundary n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedBoundary_of_outsideGraph_adj P n psi h

/--
[PeriodicGraph.bufferedInducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedInducedWiring_le_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {psi : ConfigSpace (Sym2 (P.BufferedVertex (n + 1)))} :
-- imply
  ocd_inducedWiring (P.bufferedGraph (n + 1)) (P.bufferedVertexIncl n) (P.bufferedBoundary (n + 1)) psi ≤ StatMech.Lattice.boundaryCliqueGraph (P.bufferedBoundary n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedInducedWiring_le P n psi

/--
[PeriodicGraph.freeBuffered_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBuffered_step_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (P.BufferedVertex n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * fkProb (P.bufferedGraph n) p q omega) ≤ ∑ eta, (ocd_innerRestrict (P.bufferedVertexIncl n) ⁻¹' A).indicator (fun _ => (1 : ℝ)) eta * fkProb (P.bufferedGraph (n + 1)) p q eta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBuffered_step P n hp hp1 hq hA

/--
[PeriodicGraph.wiredBuffered_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBuffered_step_eq
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (P.BufferedVertex n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ eta, (ocd_innerRestrict (P.bufferedVertexIncl n) ⁻¹' A).indicator (fun _ => (1 : ℝ)) eta * wiredFkProb (P.bufferedGraph (n + 1)) (P.bufferedBoundary (n + 1)) p q eta) ≤ ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * wiredFkProb (P.bufferedGraph n) (P.bufferedBoundary n) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBuffered_step P n hp hp1 hq hA

/--
[PeriodicGraph.continuous_bufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma continuous_bufferedRestrict_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  Continuous (P.bufferedRestrict n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.continuous_bufferedRestrict P n

/--
[PeriodicGraph.measurable_bufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma measurable_bufferedRestrict_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  Measurable (P.bufferedRestrict n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurable_bufferedRestrict P n

/--
[PeriodicGraph.monotone_bufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma monotone_bufferedRestrict_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n : ℕ} :
-- imply
  Monotone (P.bufferedRestrict n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.monotone_bufferedRestrict P n

/--
[PeriodicGraph.monotone_bufferedRestrictLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma monotone_bufferedRestrictLE_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n m : ℕ}
-- given
  (hnm : n ≤ m) :
-- imply
  Monotone (P.bufferedRestrictLE hnm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.monotone_bufferedRestrictLE P hnm

/--
[PeriodicGraph.edgeIncl_bufferedVertexInclLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma edgeIncl_bufferedVertexInclLE_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n m : ℕ}
  {e : Sym2 (P.BufferedVertex n)}
-- given
  (hnm : n ≤ m) :
-- imply
  P.edgeIncl (P.bufferedRadius m) (Sym2.map (P.bufferedVertexInclLE hnm) e) = P.edgeIncl (P.bufferedRadius n) e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.edgeIncl_bufferedVertexInclLE P hnm e

/--
[PeriodicGraph.bufferedRestrict_extendEdge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedRestrict_extendEdge_le_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n m : ℕ}
  {omega : ConfigSpace (Sym2 (P.BufferedVertex m))}
-- given
  (hnm : n ≤ m) :
-- imply
  P.bufferedRestrict n (P.extendEdge (P.bufferedRadius m) omega) = P.bufferedRestrictLE hnm omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRestrict_extendEdge_le P hnm omega

/--
[PeriodicGraph.bufferedRestrictLE_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedRestrictLE_succ_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : ℕ}
  {omega : ConfigSpace (Sym2 (P.BufferedVertex (m + 1)))}
-- given
  (hNm : N ≤ m) :
-- imply
  P.bufferedRestrictLE (hNm.trans (Nat.le_succ m)) omega = P.bufferedRestrictLE hNm (ocd_innerRestrict (P.bufferedVertexIncl m) omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRestrictLE_succ P hNm omega

/--
[PeriodicGraph.bufferedCylinder_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedCylinder_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))} :
-- imply
  IsClopen (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedCylinder_isClopen P N S

/--
[PeriodicGraph.bufferedCylinder_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedCylinder_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))} :
-- imply
  MeasurableSet (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedCylinder_measurableSet P N S

/--
[PeriodicGraph.bufferedCylinder_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma bufferedCylinder_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hS : IsIncreasing S) :
-- imply
  IsIncreasing (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedCylinder_isIncreasing P N hS

/--
[PeriodicGraph.freeBufferedMeasure_real_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBufferedMeasure_real_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (P.freeBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) = ∑ omega, (P.bufferedRestrictLE hNm ⁻¹' S).indicator (fun _ => (1 : ℝ)) omega * fkProb (P.bufferedGraph m) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_real_cylinder P hNm hp hp1 hq S

/--
[PeriodicGraph.wiredBufferedMeasure_real_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBufferedMeasure_real_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (P.wiredBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) = ∑ omega, (P.bufferedRestrictLE hNm ⁻¹' S).indicator (fun _ => (1 : ℝ)) omega * wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_real_cylinder P hNm hp hp1 hq S

/--
[PeriodicGraph.freeBufferedMeasure_step_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBufferedMeasure_step_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) ≤ (P.freeBufferedMeasure (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_step_cylinder P hNm hp hp1 hq hS

/--
[PeriodicGraph.wiredBufferedMeasure_step_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBufferedMeasure_step_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (P.wiredBufferedMeasure (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) ≤ (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_step_cylinder P hNm hp hp1 hq hS

/--
[PeriodicGraph.freeBufferedInfiniteVolume_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_isLimit_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ phi : ℕ → ℕ, StrictMono phi ∧ WeakConvergesTo (fun n => P.freeBufferedMeasure (phi n) hp hp1 hq) (P.freeBufferedInfiniteVolume hp hp1 hq) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_isLimit P hp hp1 hq

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_isLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_isLimit_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ phi : ℕ → ℕ, StrictMono phi ∧ WeakConvergesTo (fun n => P.wiredBufferedMeasure (phi n) hp hp1 hq) (P.wiredBufferedInfiniteVolume hp hp1 hq) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_isLimit P hp hp1 hq

/--
[PeriodicGraph.freeBufferedMeasure_tendsto_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBufferedMeasure_tendsto_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S)) atTop (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_tendsto_cylinder P N hp hp1 hq hS

/--
[PeriodicGraph.wiredBufferedMeasure_tendsto_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBufferedMeasure_tendsto_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S)) atTop (nhds ((P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_tendsto_cylinder P N hp hp1 hq hS

/--
[PeriodicGraph.freeBuffered_subseq_cylinder_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBuffered_subseq_cylinder_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
  (hS : IsIncreasing S) :
-- imply
  (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) = (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBuffered_subseq_cylinder_eq P hp hp1 hq nu phi hphi hconv N hS

/--
[PeriodicGraph.wiredBuffered_subseq_cylinder_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBuffered_subseq_cylinder_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
  (hS : IsIncreasing S) :
-- imply
  (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) = (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBuffered_subseq_cylinder_eq P hp hp1 hq nu phi hphi hconv N hS

/--
[PeriodicGraph.exists_bufferedLevel_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma exists_bufferedLevel_edges_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {T : Finset (Sym2 V)} :
-- imply
  ∃ N, ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_bufferedLevel_edges P T

/--
[PeriodicGraph.freeBuffered_subseq_allCylinder_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBuffered_subseq_allCylinder_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
-- imply
  (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) = (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBuffered_subseq_allCylinder_eq P hp hp1 hq nu phi hphi hconv N S

/--
[PeriodicGraph.wiredBuffered_subseq_allCylinder_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBuffered_subseq_allCylinder_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
-- imply
  (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) = (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBuffered_subseq_allCylinder_eq P hp hp1 hq nu phi hphi hconv N S

/--
[PeriodicGraph.fullCylinder_eq_bufferedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma fullCylinder_eq_bufferedCylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {s : Finset (Sym2 V)}
-- given
  (S : Set (∀ _i : s, Bool))
  (hs : ∀ e ∈ s, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
-- imply
  cylinder s S = P.bufferedCylinder N (P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder s S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.fullCylinder_eq_bufferedCylinder P N s S hs

/--
[PeriodicGraph.freeBuffered_subseq_finiteCylinder_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBuffered_subseq_finiteCylinder_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
  {s : Finset (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
  (S : Set (∀ _i : s, Bool)) :
-- imply
  (nu : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) = (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBuffered_subseq_finiteCylinder_eq P hp hp1 hq nu phi hphi hconv s S

/--
[PeriodicGraph.wiredBuffered_subseq_finiteCylinder_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBuffered_subseq_finiteCylinder_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
  {s : Finset (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
  (S : Set (∀ _i : s, Bool)) :
-- imply
  (nu : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) = (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBuffered_subseq_finiteCylinder_eq P hp hp1 hq nu phi hphi hconv s S

/--
[PeriodicGraph.freeBuffered_subseq_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBuffered_subseq_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
-- imply
  nu = P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBuffered_subseq_eq P hp hp1 hq nu phi hphi hconv

/--
[PeriodicGraph.wiredBuffered_subseq_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBuffered_subseq_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {nu : ProbabilityMeasure (ConfigSpace (Sym2 V))}
  {phi : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
-- imply
  nu = P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBuffered_subseq_eq P hp hp1 hq nu phi hphi hconv

/--
[PeriodicGraph.freeBufferedMeasure_weakConverges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBufferedMeasure_weakConverges_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  WeakConvergesTo (fun n => P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)) (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_weakConverges P hp hp1 hq

/--
[PeriodicGraph.wiredBufferedMeasure_weakConverges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBufferedMeasure_weakConverges_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  WeakConvergesTo (fun n => P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)) (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_weakConverges P hp hp1 hq

/--
[PeriodicGraph.freeBufferedMeasure_tendsto_finiteCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma freeBufferedMeasure_tendsto_finiteCylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {s : Finset (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (S : Set (∀ _i : s, Bool)) :
-- imply
  Tendsto (fun n => (P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (cylinder s S)) atTop (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (cylinder s S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_tendsto_finiteCylinder P hp hp1 hq s S

/--
[PeriodicGraph.wiredBufferedMeasure_tendsto_finiteCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean)
-/
@[path]
private lemma wiredBufferedMeasure_tendsto_finiteCylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {s : Finset (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (S : Set (∀ _i : s, Bool)) :
-- imply
  Tendsto (fun n => (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (cylinder s S)) atTop (nhds ((P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (cylinder s S))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_tendsto_finiteCylinder P hp hp1 hq s S


-- created on 2026-10-23
