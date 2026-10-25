import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.IVTranslationInvariance.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[ivt_integral_wiredShifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_integral_wiredShifted_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {n : ℕ}
  {f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∫ x, f x ∂((erg_wiredShiftedFinite hp hp1 hq g n : ProbabilityMeasure _) : Measure _)) = ∫ x, f (shift g x) ∂((wiredFiniteMeasure d n hp hp1 hq : ProbabilityMeasure _) : Measure _) := by
-- proof
  apply StatMech.FK.ivt_integral_wiredShifted hp hp1 hq g n f

/--
[ivt_integral_freeShifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_integral_freeShifted_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {n : ℕ}
  {f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∫ x, f x ∂((erg_freeShiftedFinite hp hp1 hq g n : ProbabilityMeasure _) : Measure _)) = ∫ x, f (shift g x) ∂((freeFiniteMeasure d n hp hp1 hq : ProbabilityMeasure _) : Measure _) := by
-- proof
  apply StatMech.FK.ivt_integral_freeShifted hp hp1 hq g n f

/--
[ivt_wiredShifted_weakConverges_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_wiredShifted_weakConverges_of_decay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hconv : WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq))
  (hdecay : ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
-- imply
  WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n)) (wiredInfiniteVolume d hp hp1 hq) := by
-- proof
  apply StatMech.FK.ivt_wiredShifted_weakConverges_of_decay hp hp1 hq g φ hconv hdecay

/--
[ivt_freeShifted_weakConverges_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_freeShifted_weakConverges_of_decay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hconv : WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq))
  (hdecay : ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
-- imply
  WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n)) (freeInfiniteVolume d hp hp1 hq) := by
-- proof
  apply StatMech.FK.ivt_freeShifted_weakConverges_of_decay hp hp1 hq g φ hconv hdecay

/--
[ivt_wiredIV_map_shift_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_wiredIV_map_shift_of_decay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ → WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq) → ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
-- imply
  Measure.map (shift g) (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ivt_wiredIV_map_shift_of_decay hp hp1 hq g hdecay

/--
[ivt_freeIV_map_shift_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_freeIV_map_shift_of_decay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ → WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq) → ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
-- imply
  Measure.map (shift g) (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) = (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ivt_freeIV_map_shift_of_decay hp hp1 hq g hdecay

/--
[ivt_wiredIV_isTranslationInvariant_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_wiredIV_isTranslationInvariant_of_decay_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq) → ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ivt_wiredIV_isTranslationInvariant_of_decay hp hp1 hq hdecay

/--
[ivt_freeIV_isTranslationInvariant_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_freeIV_isTranslationInvariant_of_decay_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq) → ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ivt_freeIV_isTranslationInvariant_of_decay hp hp1 hq hdecay

/--
[ivt_wiredIntegralShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_wiredIntegralShiftDecay_one_eq
  {d : ℕ}
  {p q : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ivt_wiredIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.ivt_wiredIntegralShiftDecay_one hp hp1 hq φ

/--
[ivt_freeIntegralShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_freeIntegralShiftDecay_one_eq
  {d : ℕ}
  {p q : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ivt_freeIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.ivt_freeIntegralShiftDecay_one hp hp1 hq φ

/--
[ivt_wiredIV_map_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean)
-/
@[path]
private lemma ivt_wiredIV_map_one_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Measure.map (shift (1 : Multiplicative (Site d))) (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.ivt_wiredIV_map_one hp hp1 hq


-- created on 2026-10-23
