import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.IntegralShiftDecay.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[isd_integral_comp_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_integral_comp_shift_eq
  {d : ℕ}
  {μ : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ} :
-- imply
  (∫ x, (f.compContinuous ⟨shift g, continuous_shift g⟩) x ∂(μ : Measure _)) = ∫ x, f (shift g x) ∂(μ : Measure _) := by
-- proof
  apply StatMech.FK.isd_integral_comp_shift μ g f

/--
[isd_decayFun_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_decayFun_sub_le_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {f f' : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  |isd_decayFun μ g f n - isd_decayFun μ g f' n| ≤ 2 * ‖f - f'‖ := by
-- proof
  apply StatMech.FK.isd_decayFun_sub_le μ g f f' n

/--
[isd_abs_decay_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_abs_decay_le_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {f f' : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  |isd_decayFun μ g f n| ≤ 2 * ‖f - f'‖ + |isd_decayFun μ g f' n| := by
-- proof
  apply StatMech.FK.isd_abs_decay_le μ g f f' n

/--
[isd_tendsto_decay_of_dense](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_tendsto_decay_of_dense_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {D : Set ((ConfigSpace (Sym2 (Site d))) →ᵇ ℝ)}
  {f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ}
-- given
  (hD : Dense D)
  (hdecay : ∀ f' ∈ D, Tendsto (isd_decayFun μ g f') atTop (𝓝 0)) :
-- imply
  Tendsto (isd_decayFun μ g f) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.isd_tendsto_decay_of_dense μ g hD hdecay f

/--
[isd_wiredIntegralShiftDecay_of_dense](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_wiredIntegralShiftDecay_of_dense_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdense : isd_wiredDenseDecay hp hp1 hq g φ) :
-- imply
  ivt_wiredIntegralShiftDecay hp hp1 hq g φ := by
-- proof
  apply StatMech.FK.isd_wiredIntegralShiftDecay_of_dense hp hp1 hq g φ hdense

/--
[isd_freeIntegralShiftDecay_of_dense](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_freeIntegralShiftDecay_of_dense_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdense : isd_freeDenseDecay hp hp1 hq g φ) :
-- imply
  ivt_freeIntegralShiftDecay hp hp1 hq g φ := by
-- proof
  apply StatMech.FK.isd_freeIntegralShiftDecay_of_dense hp hp1 hq g φ hdense

/--
[isd_decayFun_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_decayFun_one_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  isd_decayFun μ (1 : Multiplicative (Site d)) f n = 0 := by
-- proof
  apply StatMech.FK.isd_decayFun_one μ f n

/--
[isd_wiredDenseDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_wiredDenseDecay_one_eq
  {d : ℕ}
  {p q : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  isd_wiredDenseDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.isd_wiredDenseDecay_one hp hp1 hq φ

/--
[isd_freeDenseDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_freeDenseDecay_one_eq
  {d : ℕ}
  {p q : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  isd_freeDenseDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.isd_freeDenseDecay_one hp hp1 hq φ

/--
[isd_wiredIntegralShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_wiredIntegralShiftDecay_one_eq
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
  apply StatMech.FK.isd_wiredIntegralShiftDecay_one hp hp1 hq φ

/--
[isd_wiredIV_isTranslationInvariant_of_denseDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_wiredIV_isTranslationInvariant_of_denseDecay_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdense : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq) → isd_wiredDenseDecay hp hp1 hq g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.isd_wiredIV_isTranslationInvariant_of_denseDecay hp hp1 hq hdense

/--
[isd_freeIV_isTranslationInvariant_of_denseDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean)
-/
@[path]
private lemma isd_freeIV_isTranslationInvariant_of_denseDecay_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hdense : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq) → isd_freeDenseDecay hp hp1 hq g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.isd_freeIV_isTranslationInvariant_of_denseDecay hp hp1 hq hdense


-- created on 2026-10-23
