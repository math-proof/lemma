import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKUniquenessClose2
open MeasureTheory Set Filter Topology StatMech StatMech.FK


/--
[bcWeight_cross_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma bcWeight_cross_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p1 p2 q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q) :
-- imply
  bcWeight G C p1 q a * bcWeight G C p2 q b ≤ bcWeight G C p1 q (a ⊓ b) * bcWeight G C p2 q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcWeight_cross_p G C hp1 hp1' hp2 hp2' hle hq a b

/--
[bcProb_cross_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma bcProb_cross_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p1 p2 q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q) :
-- imply
  bcProb G C p1 q a * bcProb G C p2 q b ≤ bcProb G C p1 q (a ⊓ b) * bcProb G C p2 q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcProb_cross_p G C hp1 hp1' hp2 hp2' hle hq a b

/--
[bcProb_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma bcProb_monotone_in_p_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p1 p2 q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p1 q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p2 q ω := by
-- proof
  apply StatMech.FK.bcProb_monotone_in_p G C hp1 hp1' hp2 hp2' hle hq hA

/--
[wiredFiniteMeasure_real_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_monotone_in_p_eq
  {d : ℕ}
  {m : ℕ}
  {p1 p2 : ℝ}
  {T : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hT : IsIncreasing T)
  (hmeas : MeasurableSet (boxRestrict d m ⁻¹' T)) :
-- imply
  (wiredFiniteMeasure d m hp1 hp1' (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T) ≤ (wiredFiniteMeasure d m hp2 hp2' (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_real_monotone_in_p m hp1 hp1' hp2 hp2' hle hT hmeas

/--
[wiredFiniteMeasure_real_monotone_in_p_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_monotone_in_p_inner_eq
  {d : ℕ}
  {N m : ℕ}
  {p1 p2 : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hS : IsIncreasing S) :
-- imply
  (wiredFiniteMeasure d m hp1 hp1' (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredFiniteMeasure d m hp2 hp2' (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_real_monotone_in_p_inner N m hNm hp1 hp1' hp2 hp2' hle hS

/--
[wiredEdgeDensity_q2_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma wiredEdgeDensity_q2_monotoneOn_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  MonotoneOn (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) := by
-- proof
  apply StatMech.FK.wiredEdgeDensity_q2_monotoneOn d N eb

/--
[countable_density_ne_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma countable_density_ne_Ioo_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (heq_at_cont : ∀ p ∈ Ioo (0 : ℝ) 1, ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p → freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  {p : ℝ | p ∈ Ioo (0:ℝ) 1 ∧ freeEdgeDensity d 2 (edgeIncl d N eb) p ≠ wiredEdgeDensity d 2 (edgeIncl d N eb) p}.Countable := by
-- proof
  apply StatMech.FK.countable_density_ne_Ioo d N eb heq_at_cont

/--
[fk_uniqueness_off_countable_q2_no_hb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose2.lean)
-/
@[path]
private lemma fk_uniqueness_off_countable_q2_no_hb_eq
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (heq_at_cont : ∀ p ∈ Ioo (0 : ℝ) 1, ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p → freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))), ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) → phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.fk_uniqueness_off_countable_q2_no_hb d N eb heq_at_cont


-- created on 2026-10-23
