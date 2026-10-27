import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[itb_plus_multiOpen_full_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_plus_multiOpen_full_tendsto_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
  {T : Finset (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hφ : StrictMono φ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
-- imply
  Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)) atTop (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T))) := by
-- proof
  apply StatMech.Ising.itb_plus_multiOpen_full_tendsto hβ hh T hφ hconv

/--
[itb_boundaryDecay_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_boundaryDecay_of_homogeneous_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hhom : iti_PlusMultiHomogeneous β h g) :
-- imply
  itb_PlusMultiBoundaryDecay β h g φ := by
-- proof
  apply StatMech.Ising.itb_boundaryDecay_of_homogeneous β h g φ hconv hhom

/--
[itb_homogeneous_of_boundaryDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_homogeneous_of_boundaryDecay_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hdecay : itb_PlusMultiBoundaryDecay β h g φ) :
-- imply
  iti_PlusMultiHomogeneous β h g := by
-- proof
  apply StatMech.Ising.itb_homogeneous_of_boundaryDecay β h g φ hconv hdecay

/--
[itb_plusMultiBoundaryDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_plusMultiBoundaryDecay_one_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ) :
-- imply
  itb_PlusMultiBoundaryDecay β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.itb_plusMultiBoundaryDecay_one β h φ

/--
[itb_homogeneous_of_offCentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_homogeneous_of_offCentre_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hφ : StrictMono φ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hdom : itb_OffCentreDomination β h g) :
-- imply
  iti_PlusMultiHomogeneous β h g := by
-- proof
  apply StatMech.Ising.itb_homogeneous_of_offCentre hβ hh g hφ hconv hdom

/--
[itb_offCentreDomination_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_offCentreDomination_one_eq
  {d : ℕ}
-- given
  (β h : ℝ) :
-- imply
  itb_OffCentreDomination β h (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.Ising.itb_offCentreDomination_one β h

/--
[itb_plusState_isTranslationInvariant_of_offCentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_plusState_isTranslationInvariant_of_offCentre_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdom : ∀ g : Multiplicative (Site d), itb_OffCentreDomination β h g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.itb_plusState_isTranslationInvariant_of_offCentre hβ hh hdom

/--
[itb_plusState_isInvariantExtremePoint_of_offCentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_plusState_isInvariantExtremePoint_of_offCentre_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdom : ∀ g : Multiplicative (Site d), itb_OffCentreDomination β h g) :
-- imply
  StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.itb_plusState_isInvariantExtremePoint_of_offCentre hd hβ hh hdom

/--
[itb_plusState_isErgodic_of_offCentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean)
-/
@[path]
private lemma itb_plusState_isErgodic_of_offCentre_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdom : ∀ g : Multiplicative (Site d), itb_OffCentreDomination β h g) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.itb_plusState_isErgodic_of_offCentre hd hβ hh hdom


-- created on 2026-10-23
