import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
open StatMech StatMech.Exact3D StatMech.Exact3D.IntervalLipschitzConstant StatMech.Exact3D.StableBlockWithRemainder StatMech.Exact3D.FiniteHyperbolicSplitting StatMech.Exact3D.FiniteHyperbolicSplittingExample StatMech.Exact3D.TwoCoordinateRGData


/--
[upper_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma upper_nonneg_eq
  {L : IntervalLipschitzConstant} :
-- imply
  0 ≤ L.upper := by
-- proof
  apply StatMech.Exact3D.IntervalLipschitzConstant.upper_nonneg L

/--
[zero_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma zero_upper_eq :
-- imply
  zero.upper = 0 := by
-- proof
  apply StatMech.Exact3D.IntervalLipschitzConstant.zero_upper

/--
[ofLinearRowSum_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma ofLinearRowSum_step_eq
  {n : ℕ}
  {linear : Fin n → Fin n → ℝ}
  {enclosure : RatInterval.IntervalMatrix n n}
  {enclosure_sound : RatInterval.MatrixMem linear enclosure}
  {linear_contraction : RatInterval.RowSumContraction enclosure}
  {x : Fin n → ℝ} :
-- imply
  (ofLinearRowSum linear enclosure_sound linear_contraction).step x = fun i => RatInterval.matVec linear x i := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.ofLinearRowSum_step linear enclosure_sound linear_contraction x

/--
[remainder_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma remainder_zero_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n} :
-- imply
  S.remainder (0 : Fin n → ℝ) = 0 := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.remainder_zero S

/--
[step_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma step_zero_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n} :
-- imply
  S.step (0 : Fin n → ℝ) = 0 := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.step_zero S

/--
[iterate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_zero_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {k : ℕ} :
-- imply
  S.iterate k (0 : Fin n → ℝ) = 0 := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.iterate_zero S k

/--
[apply_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma apply_bound_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {x : Fin n → ℝ}
  {i : Fin n} :
-- imply
  |S.step x i| ≤ S.coordinateConstant * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.apply_bound S x i

/--
[coordinateConstant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma coordinateConstant_nonneg_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n} :
-- imply
  0 ≤ S.coordinateConstant := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.coordinateConstant_nonneg S

/--
[contraction_constant_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma contraction_constant_lt_one_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n} :
-- imply
  S.coordinateConstant < 1 := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.contraction_constant_lt_one S

/--
[l1StepConstant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma l1StepConstant_nonneg_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n} :
-- imply
  0 ≤ S.l1StepConstant := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.l1StepConstant_nonneg S

/--
[ofLinearRowSum_l1StepConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma ofLinearRowSum_l1StepConstant_eq
  {n : ℕ}
  {linear : Fin n → Fin n → ℝ}
  {enclosure : RatInterval.IntervalMatrix n n}
  {enclosure_sound : RatInterval.MatrixMem linear enclosure}
  {linear_contraction : RatInterval.RowSumContraction enclosure} :
-- imply
  (ofLinearRowSum linear enclosure_sound linear_contraction).l1StepConstant = (n : ℝ) * (linear_contraction.c : ℝ) := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.ofLinearRowSum_l1StepConstant linear enclosure_sound linear_contraction

/--
[step_supNormVec_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma step_supNormVec_bound_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {x : Fin n → ℝ} :
-- imply
  RatInterval.supNormVec (S.step x) ≤ S.l1StepConstant * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.step_supNormVec_bound S x

/--
[step_mem_l1_ball_of_l1StepConstant_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma step_mem_l1_ball_of_l1StepConstant_le_one_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {r : ℝ}
  {x : Fin n → ℝ}
-- given
  (hS : S.l1StepConstant ≤ 1)
  (hr : 0 ≤ r)
  (hx : RatInterval.supNormVec x ≤ r) :
-- imply
  RatInterval.supNormVec (S.step x) ≤ r := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.step_mem_l1_ball_of_l1StepConstant_le_one S hS hr hx

/--
[iterate_supNormVec_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_supNormVec_bound_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {k : ℕ}
  {x : Fin n → ℝ} :
-- imply
  RatInterval.supNormVec (S.iterate k x) ≤ S.l1StepConstant ^ k * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.iterate_supNormVec_bound S k x

/--
[tendsto_iterate_supNormVec_zero_of_l1StepConstant_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma tendsto_iterate_supNormVec_zero_of_l1StepConstant_lt_one_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {x : Fin n → ℝ}
-- given
  (hS : S.l1StepConstant < 1) :
-- imply
  Filter.Tendsto (fun k : ℕ => RatInterval.supNormVec (S.iterate k x)) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.tendsto_iterate_supNormVec_zero_of_l1StepConstant_lt_one S hS x

/--
[iterate_mem_l1_ball_of_l1StepConstant_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_mem_l1_ball_of_l1StepConstant_le_one_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {r : ℝ}
  {x : Fin n → ℝ}
  {k : ℕ}
-- given
  (hS : S.l1StepConstant ≤ 1)
  (hr : 0 ≤ r)
  (hx : RatInterval.supNormVec x ≤ r) :
-- imply
  RatInterval.supNormVec (S.iterate k x) ≤ r := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.iterate_mem_l1_ball_of_l1StepConstant_le_one S hS hr hx k

/--
[step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {thermal η t : ℝ}
  {s : Fin n → ℝ}
-- given
  (hη : 0 ≤ η)
  (hdom : S.l1StepConstant ≤ |thermal|)
  (hs : ThermalStableCone η t s) :
-- imply
  ThermalStableCone η (thermal * t) (S.step s) := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal S hη hdom hs

/--
[iterate_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal_eq
  {n : ℕ}
  {S : StableBlockWithRemainder n}
  {thermal η t : ℝ}
  {s : Fin n → ℝ}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hdom : S.l1StepConstant ≤ |thermal|)
  (hs : ThermalStableCone η t s) :
-- imply
  ThermalStableCone η (thermal ^ k * t) (S.iterate k s) := by
-- proof
  apply StatMech.Exact3D.StableBlockWithRemainder.iterate_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal S hη hdom hs k

/--
[step_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma step_origin_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n} :
-- imply
  H.step origin = origin := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.step_origin H

/--
[iterate_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_origin_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {k : ℕ} :
-- imply
  H.iterate k origin = origin := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.iterate_origin H k

/--
[certificate_retarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_retarget_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ} :
-- imply
  H.certificate scale N = (H.certificate scale M).retarget N := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_retarget H scale M N

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).thermalEigenvalue = H.thermal := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_thermalEigenvalue_eq H scale M

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_scale_eq_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).scale = scale := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_scale_eq H scale M

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).predictedExponent = predictedNu scale H.thermal := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_predictedExponent_eq H scale M

/--
[certificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_fixedPointEnclosure_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_fixedPointEnclosure H scale M

/--
[certificate_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_finiteCaseChecks_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_finiteCaseChecks H scale M

/--
[certificate_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_tailBounds_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_tailBounds H scale M

/--
[certificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_linearizationEnclosure_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_linearizationEnclosure H scale M

/--
[certificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_hyperbolicSplitting_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_hyperbolicSplitting H scale M

/--
[certificate_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_orbitEntry_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_orbitEntry H scale M

/--
[iterate_fst_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_fst_eq_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {k : ℕ}
  {x : State n} :
-- imply
  (H.iterate k x).1 = H.thermal ^ k * x.1 := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.iterate_fst_eq H k x

/--
[iterate_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_snd_eq_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {k : ℕ}
  {x : State n} :
-- imply
  (H.iterate k x).2 = H.stable.iterate k x.2 := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.iterate_snd_eq H k x

/--
[tendsto_iterate_stable_supNormVec_zero_of_l1StepConstant_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma tendsto_iterate_stable_supNormVec_zero_of_l1StepConstant_lt_one_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {x : State n}
-- given
  (hS : H.stable.l1StepConstant < 1) :
-- imply
  Filter.Tendsto (fun k : ℕ => RatInterval.supNormVec (H.iterate k x).2) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.tendsto_iterate_stable_supNormVec_zero_of_l1StepConstant_lt_one H hS x

/--
[cone_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma cone_step_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {η : ℝ}
  {x : State n}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η (H.step x) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.cone_step H hη hx

/--
[cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma cone_iterate_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {η : ℝ}
  {x : State n}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η (H.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.cone_iterate H hη hx k

/--
[rgMap_iterate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma rgMap_iterate_eq_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {k : ℕ}
  {x : State n} :
-- imply
  ((H.rgMap scale).map^[k]) x = H.iterate k x := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.rgMap_iterate_eq H scale k x

/--
[rgMap_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma rgMap_cone_iterate_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {η : ℝ}
  {x : State n}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η (((H.rgMap scale).map^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.rgMap_cone_iterate H scale hη hx k

/--
[tendsto_rgMap_stable_supNormVec_zero_of_l1StepConstant_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma tendsto_rgMap_stable_supNormVec_zero_of_l1StepConstant_lt_one_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {x : State n}
-- given
  (hS : H.stable.l1StepConstant < 1) :
-- imply
  Filter.Tendsto (fun k : ℕ => RatInterval.supNormVec ((((H.rgMap scale).map^[k]) x).2)) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.tendsto_rgMap_stable_supNormVec_zero_of_l1StepConstant_lt_one H scale hS x

/--
[certificate_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_cone_iterate_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {η : ℝ}
  {x : (H.certificate scale M).H.carrier}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : H.cone η x) :
-- imply
  H.cone η ((((H.certificate scale M).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_cone_iterate H scale M hη hx k

/--
[tendsto_certificate_stable_supNormVec_zero_of_l1StepConstant_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma tendsto_certificate_stable_supNormVec_zero_of_l1StepConstant_lt_one_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {x : (H.certificate scale M).H.carrier}
-- given
  (hS : H.stable.l1StepConstant < 1) :
-- imply
  Filter.Tendsto (fun k : ℕ => RatInterval.supNormVec ((((H.certificate scale M).R.map)^[k]) x).2) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.tendsto_certificate_stable_supNormVec_zero_of_l1StepConstant_lt_one H scale M hS x

/--
[certificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_valid_of_bridge H scale M correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_hasCriticalNu_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_rgToExponentBridge_of_hasCriticalNu H scale M correlationLength hν

/--
[certificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_valid_of_hasCriticalNu_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_valid_of_hasCriticalNu H scale M correlationLength hν

/--
[certificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_hasCriticalNu_of_bridge H scale M correlationLength hbridge

/--
[exactScaleObservable_eq_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma exactScaleObservable_eq_power_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {β : ℝ} :
-- imply
  H.exactScaleObservable scale M β = Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.exactScaleObservable_eq_power H scale M β

/--
[certificate_rgToExponentBridge_exactScaleObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_exactScaleObservable_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).RGToExponentBridge (H.exactScaleObservable scale M) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_rgToExponentBridge_exactScaleObservable H scale M

/--
[certificate_valid_exactScaleObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_valid_exactScaleObservable_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  (H.certificate scale M).Valid (H.exactScaleObservable scale M) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_valid_exactScaleObservable H scale M

/--
[certificate_hasCriticalNu_exactScaleObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_exactScaleObservable_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι} :
-- imply
  HasCriticalNu M (H.exactScaleObservable scale M) (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_hasCriticalNu_exactScaleObservable H scale M

/--
[certificate_rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent H scale M hpred hbridge

/--
[certificate_valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_valid_of_bridge_congr_predictedExponent H scale M hpred hbridge

/--
[certificate_hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_congr_predictedExponent_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_hasCriticalNu_of_bridge_congr_predictedExponent H scale M hpred hbridge

/--
[certificate_retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC)
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
-- imply
  (H.certificate scale N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_retarget_rgToExponentBridge H scale M N hβc hbridge

/--
[certificate_retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC)
  (hvalid : (H.certificate scale M).Valid correlationLength) :
-- imply
  (H.certificate scale N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_retarget_valid H scale M N hβc hvalid

/--
[certificate_retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC)
  (hν : HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent) :
-- imply
  HasCriticalNu N correlationLength (H.certificate scale N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_retarget_hasCriticalNu H scale M N hβc hν

/--
[certificate_retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_retarget_rgToExponentBridge_iff_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength ↔ (H.certificate scale N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_retarget_rgToExponentBridge_iff H scale M N hβc

/--
[certificate_retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_retarget_valid_iff_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  (H.certificate scale M).Valid correlationLength ↔ (H.certificate scale N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_retarget_valid_iff H scale M N hβc

/--
[certificate_retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_retarget_hasCriticalNu_iff_eq
  {n : ℕ}
  {H : FiniteHyperbolicSplitting n}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent ↔ HasCriticalNu N correlationLength (H.certificate scale N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplitting.certificate_retarget_hasCriticalNu_iff H scale M N hβc

/--
[stableLinear_mem_enclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma stableLinear_mem_enclosure_eq :
-- imply
  RatInterval.MatrixMem stableLinear stableEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplittingExample.stableLinear_mem_enclosure

/--
[stableBlock_linear_contraction_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma stableBlock_linear_contraction_c_eq :
-- imply
  stableBlock.linear_contraction.c = (1 / 2 : ℚ) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplittingExample.stableBlock_linear_contraction_c

/--
[stableBlock_remainder_lipschitz_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma stableBlock_remainder_lipschitz_upper_eq :
-- imply
  stableBlock.remainder_lipschitz.upper = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplittingExample.stableBlock_remainder_lipschitz_upper

/--
[stableBlock_l1StepConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma stableBlock_l1StepConstant_eq :
-- imply
  stableBlock.l1StepConstant = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplittingExample.stableBlock_l1StepConstant

/--
[splitting_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma splitting_cone_iterate_eq
  {η : ℝ}
  {x : FiniteHyperbolicSplitting.State 1}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : splitting.cone η x) :
-- imply
  splitting.cone η (splitting.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplittingExample.splitting_cone_iterate hη hx k

/--
[splittingFromRowSum_certificate_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma splittingFromRowSum_certificate_cone_iterate_eq
  {η : ℝ}
  {x : (splittingFromRowSum.certificate scale model).H.carrier}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : splittingFromRowSum.cone η x) :
-- imply
  splittingFromRowSum.cone η ((((splittingFromRowSum.certificate scale model).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplittingExample.splittingFromRowSum_certificate_cone_iterate hη hx k

/--
[certificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_fixedPointEnclosure_eq_2 :
-- imply
  certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteHyperbolicSplittingExample.certificate_fixedPointEnclosure

/--
[iterate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma iterate_eq_eq
  {D : TwoCoordinateRGData}
  {n : ℕ}
  {x : ℝ × ℝ} :
-- imply
  D.iterate n x = (D.thermal ^ n * x.1, D.stable ^ n * x.2) := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.iterate_eq D n x

/--
[stable_iterate_abs_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma stable_iterate_abs_eq_eq
  {D : TwoCoordinateRGData}
  {n : ℕ}
  {s : ℝ} :
-- imply
  |(D.iterate n (0, s)).2| = |D.stable| ^ n * |s| := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.stable_iterate_abs_eq D n s

/--
[stable_multiplier_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma stable_multiplier_lt_one_eq
  {D : TwoCoordinateRGData} :
-- imply
  |D.stable| < 1 := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.stable_multiplier_lt_one D

/--
[thermal_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma thermal_pos_eq
  {D : TwoCoordinateRGData} :
-- imply
  0 < D.thermal := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.thermal_pos D

/--
[abs_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma abs_thermal_eq_eq
  {D : TwoCoordinateRGData} :
-- imply
  |D.thermal| = D.thermal := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.abs_thermal_eq D

/--
[stable_abs_le_thermal_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma stable_abs_le_thermal_abs_eq
  {D : TwoCoordinateRGData} :
-- imply
  |D.stable| ≤ |D.thermal| := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.stable_abs_le_thermal_abs D

/--
[thermalCone_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma thermalCone_step_eq
  {D : TwoCoordinateRGData}
  {K : ℝ}
  {x : ℝ × ℝ}
-- given
  (hK : 0 ≤ K)
  (hx : D.thermalCone K x) :
-- imply
  D.thermalCone K (D.rgMap.map x) := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.thermalCone_step hK hx

/--
[thermalCone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma thermalCone_iterate_eq
  {D : TwoCoordinateRGData}
  {K : ℝ}
  {x : ℝ × ℝ}
  {n : ℕ}
-- given
  (hK : 0 ≤ K)
  (hx : D.thermalCone K x) :
-- imply
  D.thermalCone K (D.iterate n x) := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.thermalCone_iterate hK hx n

/--
[exactScaleObservable_eq_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma exactScaleObservable_eq_power_eq_2
  {D : TwoCoordinateRGData}
  {β : ℝ} :
-- imply
  D.exactScaleObservable β = Real.exp (-D.certificate.predictedExponent * Real.log (D.model.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.exactScaleObservable_eq_power D β

/--
[bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma bridge_eq
  {D : TwoCoordinateRGData} :
-- imply
  D.certificate.RGToExponentBridge D.exactScaleObservable := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.bridge D

/--
[certificate_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma certificate_valid_eq
  {D : TwoCoordinateRGData} :
-- imply
  D.certificate.Valid D.exactScaleObservable := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.certificate_valid D

/--
[hasCriticalNu_eq_predicted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean)
-/
@[path]
private lemma hasCriticalNu_eq_predicted_eq
  {D : TwoCoordinateRGData} :
-- imply
  HasCriticalNu D.model D.exactScaleObservable D.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.TwoCoordinateRGData.hasCriticalNu_eq_predicted D


-- created on 2026-10-23
