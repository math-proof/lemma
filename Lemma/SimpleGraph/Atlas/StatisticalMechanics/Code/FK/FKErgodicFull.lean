import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKErgodicFull.Part2
open MeasureTheory Filter Topology StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[erg_map_eq_of_translated_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean)
-/
@[path]
private lemma erg_map_eq_of_translated_converges_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {T : ConfigSpace E → ConfigSpace E}
-- given
  (hT : Continuous T)
  (hconv : WeakConvergesTo μ ν)
  (hshift : WeakConvergesTo (fun n => (μ n).map hT.measurable.aemeasurable) ν) :
-- imply
  ν.map hT.measurable.aemeasurable = ν := by
-- proof
  apply StatMech.FK.erg_map_eq_of_translated_converges μ ν hT hconv hshift

/--
[erg_measure_map_eq_of_translated_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean)
-/
@[path]
private lemma erg_measure_map_eq_of_translated_converges_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
  {ν : ProbabilityMeasure (ConfigSpace E)}
  {T : ConfigSpace E → ConfigSpace E}
-- given
  (hT : Continuous T)
  (hconv : WeakConvergesTo μ ν)
  (hshift : WeakConvergesTo (fun n => (μ n).map hT.measurable.aemeasurable) ν) :
-- imply
  Measure.map T (ν : Measure (ConfigSpace E)) = (ν : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FK.erg_measure_map_eq_of_translated_converges μ ν hT hconv hshift

/--
[erg_wiredIV_map_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean)
-/
@[path]
private lemma erg_wiredIV_map_shift_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hshift : ∀ φ : ℕ → ℕ, StrictMono φ → WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq) → WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n)) (wiredInfiniteVolume d hp hp1 hq)) :
-- imply
  Measure.map (shift g) (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.erg_wiredIV_map_shift hp hp1 hq g hshift

/--
[erg_freeIV_map_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean)
-/
@[path]
private lemma erg_freeIV_map_shift_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hshift : ∀ φ : ℕ → ℕ, StrictMono φ → WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq) → WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n)) (freeInfiniteVolume d hp hp1 hq)) :
-- imply
  Measure.map (shift g) (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) = (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.erg_freeIV_map_shift hp hp1 hq g hshift

/--
[erg_wiredIV_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean)
-/
@[path]
private lemma erg_wiredIV_isTranslationInvariant_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hshift : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq) → WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n)) (wiredInfiniteVolume d hp hp1 hq)) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.erg_wiredIV_isTranslationInvariant hp hp1 hq hshift

/--
[erg_freeIV_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicFull.lean)
-/
@[path]
private lemma erg_freeIV_isTranslationInvariant_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hshift : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq) → WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n)) (freeInfiniteVolume d hp hp1 hq)) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.erg_freeIV_isTranslationInvariant hp hp1 hq hshift


-- created on 2026-10-23
