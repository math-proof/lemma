import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.IsingBoxSqueeze
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[ibs_isClopen_spinUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_isClopen_spinUp_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  IsClopen {ω : ConfigSpace (Site d) | ω x = true} := by
-- proof
  apply StatMech.Ising.ibs_isClopen_spinUp x

/--
[ibs_measurableSet_spinUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_measurableSet_spinUp_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Site d) | ω x = true} := by
-- proof
  apply StatMech.Ising.ibs_measurableSet_spinUp x

/--
[ibs_integral_coordBcf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_integral_coordBcf_eq
  {d : ℕ}
  {x : Site d}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ] :
-- imply
  (∫ ω, pstc_coordBcf x ω ∂μ) = μ.real {ω | ω x = true} := by
-- proof
  apply StatMech.Ising.ibs_integral_coordBcf x μ

/--
[ibs_coordBcf_comp_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_coordBcf_comp_shift_eq
  {d : ℕ}
  {x : Site d}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Site d)} :
-- imply
  pstc_coordBcf x (shift g ω) = pstc_coordBcf (g⁻¹ • x) ω := by
-- proof
  apply StatMech.Ising.ibs_coordBcf_comp_shift x g ω

/--
[ibs_decayFun_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_decayFun_coord_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {x : Site d}
  {n : ℕ} :
-- imply
  pstc_decayFun μ g (pstc_coordBcf x) n = ((μ n : Measure (ConfigSpace (Site d))).real {ω | ω x = true}) - ((μ n : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) := by
-- proof
  apply StatMech.Ising.ibs_decayFun_coord μ g x n

/--
[ibs_plus_siteProb_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_plus_siteProb_tendsto_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
  {x : Site d}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
-- imply
  Tendsto (fun n => (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true}) atTop (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})) := by
-- proof
  apply StatMech.Ising.ibs_plus_siteProb_tendsto β h φ x hconv

/--
[ibs_minus_siteProb_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_minus_siteProb_tendsto_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
  {x : Site d}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h)) :
-- imply
  Tendsto (fun n => (minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true}) atTop (𝓝 ((minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})) := by
-- proof
  apply StatMech.Ising.ibs_minus_siteProb_tendsto β h φ x hconv

/--
[ibs_plus_coord_decay_of_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_plus_coord_decay_of_density_eq_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
  {g : Multiplicative (Site d)}
  {x : Site d}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hdens : (plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true} = (plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) :
-- imply
  Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (pstc_coordBcf x)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.ibs_plus_coord_decay_of_density_eq β h φ g x hconv hdens

/--
[ibs_minus_coord_decay_of_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_minus_coord_decay_of_density_eq_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
  {g : Multiplicative (Site d)}
  {x : Site d}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h))
  (hdens : (minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true} = (minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) :
-- imply
  Tendsto (pstc_decayFun (fun n => minusMeasure d (φ n) β h) g (pstc_coordBcf x)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.ibs_minus_coord_decay_of_density_eq β h φ g x hconv hdens

/--
[ibs_boundaryFraction_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_boundaryFraction_nonneg_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  0 ≤ ibs_boundaryFraction d n := by
-- proof
  apply StatMech.Ising.ibs_boundaryFraction_nonneg d n

/--
[ibs_boundaryFraction_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_boundaryFraction_tendsto_zero_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (ibs_boundaryFraction d) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.ibs_boundaryFraction_tendsto_zero hd

/--
[ibs_boundaryFraction_comp_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_boundaryFraction_comp_tendsto_zero_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (hd : 1 ≤ d)
  (hφ : StrictMono φ) :
-- imply
  Tendsto (fun n => ibs_boundaryFraction d (φ n)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.ibs_boundaryFraction_comp_tendsto_zero hd hφ

/--
[ibs_decay_of_boundaryBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_decay_of_boundaryBound_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
  {φ : ℕ → ℕ}
  {C : ℝ}
-- given
  (hd : 1 ≤ d)
  (hφ : StrictMono φ)
  (hbound : ∀ n, |pstc_decayFun (fun n => μ (φ n)) g f n| ≤ C * ibs_boundaryFraction d (φ n)) :
-- imply
  Tendsto (pstc_decayFun (fun n => μ (φ n)) g f) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.ibs_decay_of_boundaryBound μ g f hd hφ C hbound

/--
[ibs_plusCylinderDecay_of_boundaryInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_plusCylinderDecay_of_boundaryInfluence_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hφ : StrictMono φ)
  (hbi : ibs_PlusBoundaryInfluence β h g φ) :
-- imply
  pstc_PlusCylinderDecay β h g φ := by
-- proof
  apply StatMech.Ising.ibs_plusCylinderDecay_of_boundaryInfluence β h g φ hd hφ hbi

/--
[ibs_minusCylinderDecay_of_boundaryInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_minusCylinderDecay_of_boundaryInfluence_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hφ : StrictMono φ)
  (hbi : ibs_MinusBoundaryInfluence β h g φ) :
-- imply
  pstc_MinusCylinderDecay β h g φ := by
-- proof
  apply StatMech.Ising.ibs_minusCylinderDecay_of_boundaryInfluence β h g φ hd hφ hbi

/--
[ibs_plusBoundaryInfluence_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_plusBoundaryInfluence_one_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ) :
-- imply
  ibs_PlusBoundaryInfluence β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.ibs_plusBoundaryInfluence_one β h φ

/--
[ibs_minusBoundaryInfluence_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_minusBoundaryInfluence_one_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ) :
-- imply
  ibs_MinusBoundaryInfluence β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.ibs_minusBoundaryInfluence_one β h φ

/--
[ibs_plusCylinderDecay_one_via_squeeze](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_plusCylinderDecay_one_via_squeeze_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hφ : StrictMono φ) :
-- imply
  pstc_PlusCylinderDecay β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.ibs_plusCylinderDecay_one_via_squeeze β h hd hφ

/--
[ibs_plusState_isTranslationInvariant_of_boundaryInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_plusState_isTranslationInvariant_of_boundaryInfluence_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) → ibs_PlusBoundaryInfluence β h g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.ibs_plusState_isTranslationInvariant_of_boundaryInfluence β h hd hbi

/--
[ibs_plusState_ergodic_extreme_of_boundaryInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_plusState_ergodic_extreme_of_boundaryInfluence_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) → ibs_PlusBoundaryInfluence β h g φ) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.ibs_plusState_ergodic_extreme_of_boundaryInfluence β h hd hβ hh hbi

/--
[ibs_minusState_ergodic_extreme_of_boundaryInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean)
-/
@[path]
private lemma ibs_minusState_ergodic_extreme_of_boundaryInfluence_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
  (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) → ibs_MinusBoundaryInfluence β h g φ) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.ibs_minusState_ergodic_extreme_of_boundaryInfluence β h hd hβ hh hdlr hbi


-- created on 2026-10-23
