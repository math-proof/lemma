import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangGibbsUniqueness
open Filter Finset MeasureTheory ProbabilityTheory Set Topology StatMech StatMech.FrontierA


/--
[fvWeight_hasDerivAt_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma fvWeight_hasDerivAt_field_eq
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  HasDerivAt (fun t => fvWeight eta n B beta t tau) (fvWeight eta n B beta h tau * (beta * ∑ x ∈ boxFinset d n, spin (glue eta tau) x)) h := by
-- proof
  apply StatMech.FrontierA.fvWeight_hasDerivAt_field eta n B beta h tau

/--
[fvZ_hasDerivAt_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma fvZ_hasDerivAt_field_eq
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun t => fvZ eta n B beta t) (∑ tau : {x // x ∈ box d n} → Bool, fvWeight eta n B beta h tau * (beta * ∑ x ∈ boxFinset d n, spin (glue eta tau) x)) h := by
-- proof
  apply StatMech.FrontierA.fvZ_hasDerivAt_field eta n B beta h

/--
[fvBoxAverageSpin_eq_completion_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma fvBoxAverageSpin_eq_completion_sum_eq
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ) :
-- imply
  fvBoxAverageSpin eta n B beta h = (∑ tau : {x // x ∈ box d n} → Bool, fvProb eta n B beta h tau * (∑ x ∈ boxFinset d n, spin (glue eta tau) x)) / ((boxFinset d n).card : ℝ) := by
-- proof
  apply StatMech.FrontierA.fvBoxAverageSpin_eq_completion_sum eta n B beta h

/--
[fvBoxPressure_hasDerivAt_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma fvBoxPressure_hasDerivAt_field_eq
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun t => fvBoxPressure eta n B beta t) (beta * fvBoxAverageSpin eta n B beta h) h := by
-- proof
  apply StatMech.FrontierA.fvBoxPressure_hasDerivAt_field eta n B beta h

/--
[plusBoxPressure_hasDerivAt_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma plusBoxPressure_hasDerivAt_field_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun t => fvBoxPressure (plusField d) n (bondFinsetTouch d n) beta t) (beta * fvBoxAverageSpin (plusField d) n (bondFinsetTouch d n) beta h) h := by
-- proof
  apply StatMech.FrontierA.plusBoxPressure_hasDerivAt_field d n beta h

/--
[minusBoxPressure_hasDerivAt_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma minusBoxPressure_hasDerivAt_field_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun t => fvBoxPressure (minusField d) n (bondFinsetTouch d n) beta t) (beta * fvBoxAverageSpin (minusField d) n (bondFinsetTouch d n) beta h) h := by
-- proof
  apply StatMech.FrontierA.minusBoxPressure_hasDerivAt_field d n beta h

/--
[fvBoxPressure_convexOn_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma fvBoxPressure_convexOn_field_eq
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {beta : ℝ} :
-- imply
  ConvexOn ℝ Set.univ (fun h => fvBoxPressure eta n B beta h) := by
-- proof
  apply StatMech.FrontierA.fvBoxPressure_convexOn_field eta n B beta

/--
[isingBoxPressureLimit_hasDerivAt_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma isingBoxPressureLimit_hasDerivAt_pos_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  ∃ L : ℝ, HasDerivAt (isingBoxPressureLimit d hd beta) L h := by
-- proof
  apply StatMech.FrontierA.isingBoxPressureLimit_hasDerivAt_pos d hd hbeta hh

/--
[isingBoxPressureLimit_oneSided_eq_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma isingBoxPressureLimit_oneSided_eq_pos_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  pressureLeftDeriv (isingBoxPressureLimit d hd beta) h = pressureRightDeriv (isingBoxPressureLimit d hd beta) h := by
-- proof
  apply StatMech.FrontierA.isingBoxPressureLimit_oneSided_eq_pos d hd hbeta hh

/--
[plusBoxAverageSpin_tendsto_pressureDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma plusBoxAverageSpin_tendsto_pressureDeriv_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n => beta * fvBoxAverageSpin (plusField d) n (bondFinsetTouch d n) beta h) atTop (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h)) := by
-- proof
  apply StatMech.FrontierA.plusBoxAverageSpin_tendsto_pressureDeriv d hd hbeta hh

/--
[minusBoxAverageSpin_tendsto_pressureDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma minusBoxAverageSpin_tendsto_pressureDeriv_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n => beta * fvBoxAverageSpin (minusField d) n (bondFinsetTouch d n) beta h) atTop (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h)) := by
-- proof
  apply StatMech.FrontierA.minusBoxAverageSpin_tendsto_pressureDeriv d hd hbeta hh

/--
[integral_spin_eq_origin_of_translationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma integral_spin_eq_origin_of_translationInvariant_eq
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {x : Site d}
-- given
  (hti : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  (∫ omega, spin omega x ∂mu) = ∫ omega, spin omega (StatMech.Percolation.origin d) ∂mu := by
-- proof
  apply StatMech.FrontierA.integral_spin_eq_origin_of_translationInvariant mu hti x

/--
[plusState_spin_le_fvBoxAverageSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma plusState_spin_le_fvBoxAverageSpin_eq
  {d n : ℕ}
  {beta h : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hti : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d beta h : Measure (ConfigSpace (Site d)))) :
-- imply
  (∫ omega, spin omega (StatMech.Percolation.origin d) ∂(plusState d beta h : Measure (ConfigSpace (Site d)))) ≤ fvBoxAverageSpin (plusField d) n (bondFinsetTouch d n) beta h := by
-- proof
  apply StatMech.FrontierA.plusState_spin_le_fvBoxAverageSpin d n hbeta hh hti

/--
[fvBoxAverageSpin_le_minusState_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma fvBoxAverageSpin_le_minusState_spin_eq
  {d n : ℕ}
  {beta h : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hdlr : IsDLRState d beta h (minusState d beta h : Measure (ConfigSpace (Site d))))
  (hti : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d beta h : Measure (ConfigSpace (Site d)))) :
-- imply
  fvBoxAverageSpin (minusField d) n (bondFinsetTouch d n) beta h ≤ ∫ omega, spin omega (StatMech.Percolation.origin d) ∂(minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.fvBoxAverageSpin_le_minusState_spin d n hbeta hh hdlr hti

/--
[plusState_eq_minusState_of_positive_field_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma plusState_eq_minusState_of_positive_field_aux_eq
  {d : ℕ}
  {beta h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hminusDLR : IsDLRState d beta h (minusState d beta h : Measure (ConfigSpace (Site d))))
  (hminusTI : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d beta h : Measure (ConfigSpace (Site d)))) :
-- imply
  (plusState d beta h : Measure (ConfigSpace (Site d))) = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.plusState_eq_minusState_of_positive_field_aux d hd hbeta hh hminusDLR hminusTI

/--
[gibbs_unique_of_positive_field_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma gibbs_unique_of_positive_field_aux_eq
  {d : ℕ}
  {beta h : ℝ}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hminusDLR : IsDLRState d beta h (minusState d beta h : Measure (ConfigSpace (Site d))))
  (hminusTI : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d beta h : Measure (ConfigSpace (Site d))))
  (hmu : IsDLRState d beta h mu) :
-- imply
  mu = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.gibbs_unique_of_positive_field_aux d hd hbeta hh hminusDLR hminusTI mu hmu

/--
[specApply_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma specApply_flipConfig_eq
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
  {omega : ConfigSpace (Site d)}
-- given
  (beta h : ℝ) :
-- imply
  specApply n B beta (-h) (f : ConfigSpace (Site d) → ℝ) (flipConfig omega) = specApply n B beta h (fun eta => f (flipConfig eta)) omega := by
-- proof
  apply StatMech.FrontierA.specApply_flipConfig n B beta h f omega

/--
[isDLRState_map_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma isDLRState_map_flipConfig_eq
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (beta h : ℝ)
  (hmu : IsDLRState d beta h mu) :
-- imply
  IsDLRState d beta (-h) (Measure.map flipConfig mu) := by
-- proof
  apply StatMech.FrontierA.isDLRState_map_flipConfig beta h mu hmu

/--
[plusState_eq_minusState_of_positive_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma plusState_eq_minusState_of_positive_field_eq
  {d : ℕ}
  {beta h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  (plusState d beta h : Measure (ConfigSpace (Site d))) = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.plusState_eq_minusState_of_positive_field d hd hbeta hh

/--
[gibbs_unique_of_positive_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma gibbs_unique_of_positive_field_eq
  {d : ℕ}
  {beta h : ℝ}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hmu : IsDLRState d beta h mu) :
-- imply
  mu = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.gibbs_unique_of_positive_field d hd hbeta hh mu hmu

/--
[map_flipConfig_map_flipConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma map_flipConfig_map_flipConfig_eq
  {mu : Measure (ConfigSpace (Site d))} :
-- imply
  Measure.map flipConfig (Measure.map flipConfig mu) = mu := by
-- proof
  apply StatMech.FrontierA.map_flipConfig_map_flipConfig mu

/--
[gibbs_states_eq_of_negative_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma gibbs_states_eq_of_negative_field_eq
  {d : ℕ}
  {beta h : ℝ}
  {mu nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : h < 0)
  (hmu : IsDLRState d beta h mu)
  (hnu : IsDLRState d beta h nu) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.gibbs_states_eq_of_negative_field d hd hbeta hh mu nu hmu hnu

/--
[plusState_eq_minusState_of_nonzero_field_of_pos_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma plusState_eq_minusState_of_nonzero_field_of_pos_beta_eq
  {d : ℕ}
  {beta h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : h ≠ 0) :
-- imply
  (plusState d beta h : Measure (ConfigSpace (Site d))) = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.plusState_eq_minusState_of_nonzero_field_of_pos_beta d hd hbeta hh

/--
[gibbs_unique_of_nonzero_field_of_pos_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma gibbs_unique_of_nonzero_field_of_pos_beta_eq
  {d : ℕ}
  {beta h : ℝ}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hh : h ≠ 0)
  (hmu : IsDLRState d beta h mu) :
-- imply
  mu = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.gibbs_unique_of_nonzero_field_of_pos_beta d hd hbeta hh mu hmu

/--
[plusState_eq_minusState_of_nonzero_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma plusState_eq_minusState_of_nonzero_field_eq
  {d : ℕ}
  {beta h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 ≤ beta)
  (hh : h ≠ 0) :
-- imply
  (plusState d beta h : Measure (ConfigSpace (Site d))) = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.plusState_eq_minusState_of_nonzero_field d hd hbeta hh

/--
[gibbs_unique_of_nonzero_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangGibbsUniqueness.lean)
-/
@[path]
private lemma gibbs_unique_of_nonzero_field_eq
  {d : ℕ}
  {beta h : ℝ}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 ≤ beta)
  (hh : h ≠ 0)
  (hmu : IsDLRState d beta h mu) :
-- imply
  mu = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.gibbs_unique_of_nonzero_field d hd hbeta hh mu hmu


-- created on 2026-10-23
