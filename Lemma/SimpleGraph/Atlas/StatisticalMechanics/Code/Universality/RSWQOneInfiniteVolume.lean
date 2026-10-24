import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWQOneInfiniteVolume
open Set SimpleGraph MeasureTheory Filter Topology StatMech StatMech.Universality


/--
[rq1_boxRestrictLE_event_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneInfiniteVolume.lean)
-/
@[path]
private lemma rq1_boxRestrictLE_event_dependsOn_eq
  {d : ℕ}
  {N m : ℕ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hS : _root_.DependsOn (S.indicator (fun _ => (1 : ℝ))) ((boxGraph d N).edgeFinset : Set (Sym2 (boxVerts d N)))) :
-- imply
  _root_.DependsOn ((boxRestrictLE d hNm ⁻¹' S).indicator (fun _ => (1 : ℝ))) ((boxGraph d m).edgeFinset : Set (Sym2 (boxVerts d m))) := by
-- proof
  apply StatMech.Universality.rq1_boxRestrictLE_event_dependsOn hNm S hS

/--
[rq1_wiredFinite_graphCylinder_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneInfiniteVolume.lean)
-/
@[path]
private lemma rq1_wiredFinite_graphCylinder_eq_bernoulli_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : _root_.DependsOn (S.indicator (fun _ => (1 : ℝ))) ((boxGraph d N).edgeFinset : Set (Sym2 (boxVerts d N)))) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) = (bernoulliProductMeasure (E := Sym2 (Site d)) (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.Universality.rq1_wiredFinite_graphCylinder_eq_bernoulli hNm hp hp1 S hS

/--
[rq1_wiredInfiniteVolume_graphCylinder_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneInfiniteVolume.lean)
-/
@[path]
private lemma rq1_wiredInfiniteVolume_graphCylinder_eq_bernoulli_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : _root_.DependsOn (S.indicator (fun _ => (1 : ℝ))) ((boxGraph d N).edgeFinset : Set (Sym2 (boxVerts d N)))) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) = (bernoulliProductMeasure (E := Sym2 (Site d)) (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.Universality.rq1_wiredInfiniteVolume_graphCylinder_eq_bernoulli N hp hp1 S hS

/--
[rq1_wiredInfiniteVolume_centeredSquare_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneInfiniteVolume.lean)
-/
@[path]
private lemma rq1_wiredInfiniteVolume_centeredSquare_eq_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site 2)))).real (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) = rba_selfDualMeasure.real (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
-- proof
  apply StatMech.Universality.rq1_wiredInfiniteVolume_centeredSquare_eq n

/--
[rq1_wiredInfiniteVolume_centeredSquare_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneInfiniteVolume.lean)
-/
@[path]
private lemma rq1_wiredInfiniteVolume_centeredSquare_half_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 2 ≤ (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site 2)))).real (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
-- proof
  apply StatMech.Universality.rq1_wiredInfiniteVolume_centeredSquare_half n hn


-- created on 2026-10-23
