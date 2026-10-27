import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
open MeasureTheory Filter Topology SimpleGraph StatMech StatMech.FK


/--
[mvl_free_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneVolumeLimit.lean)
-/
@[path]
private lemma mvl_free_tendsto_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) := by
-- proof
  apply StatMech.FK.mvl_free_tendsto N hp hp1 hS

/--
[mvl_wired_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneVolumeLimit.lean)
-/
@[path]
private lemma mvl_wired_tendsto_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) := by
-- proof
  apply StatMech.FK.mvl_wired_tendsto N hp hp1 hS

/--
[mvl_infiniteVolume_extremal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneVolumeLimit.lean)
-/
@[path]
private lemma mvl_infiniteVolume_extremal_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) ∧ Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) ∧ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.mvl_infiniteVolume_extremal N hp hp1 hS

/--
[mvl_infiniteVolume_extremal_subseq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneVolumeLimit.lean)
-/
@[path]
private lemma mvl_infiniteVolume_extremal_subseq_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  ∃ (ψ : ℕ → ℕ) (φ0 φ1 : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))), StrictMono ψ ∧ φ0 = freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) ∧ φ1 = wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) ∧ Tendsto (fun m => (freeFiniteMeasure d (ψ m) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((φ0 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) ∧ Tendsto (fun m => (wiredFiniteMeasure d (ψ m) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((φ1 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) ∧ (φ0 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (φ1 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.mvl_infiniteVolume_extremal_subseq N hp hp1 hS


-- created on 2026-10-23
