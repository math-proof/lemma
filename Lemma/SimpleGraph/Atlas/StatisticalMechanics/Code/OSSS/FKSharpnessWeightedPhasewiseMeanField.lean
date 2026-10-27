import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhasewiseMeanField.Part2
open Finset Set Filter Topology MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField


/--
[weightedPhaseFinite_shell_le_wiredFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedPhaseFinite_shell_le_wiredFinite_eq
  {d k R : Nat}
  {a : P}
  {Jmax : Real}
  {q beta p : Real}
-- given
  (hkR : k <= R)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hJhi : forall e, phaseJ a e <= Jmax)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hpmax : 1 - Real.exp (-(beta * Jmax)) <= p) :
-- imply
  ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) <= (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedPhaseFinite_shell_le_wiredFinite d k R hkR phaseJ a hJ Jmax hJhi q beta p hq hbeta hp hp1 hpmax

/--
[weightedPhaseInfiniteTheta_le_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedPhaseInfiniteTheta_le_fkTheta_eq
  {d : Nat}
  {a : P}
  {Jmax : Real}
  {q beta p : Real}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hJhi : forall e, phaseJ a e <= Jmax)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hpmax : 1 - Real.exp (-(beta * Jmax)) <= p) :
-- imply
  weightedPhaseInfiniteTheta d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta <= fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedPhaseInfiniteTheta_le_fkTheta d phaseJ a hJ Jmax hJhi q beta p hq hbeta hp hp1 hpmax

/--
[phaseCoupling_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma phaseCoupling_upper_eq
  {d : Nat}
  {J : Sym2 (Site d) -> Real}
  {phase : Site d -> P}
  {phaseJ : P -> Sym2 (Site d) -> Real}
  {Jmax : Real}
-- given
  (hcov : PhaseCovariant J phase phaseJ)
  (hsurj : Function.Surjective phase)
  (hJhi : forall e, J e <= Jmax) :
-- imply
  forall a e, phaseJ a e <= Jmax := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.phaseCoupling_upper hcov hsurj hJhi

/--
[weightedThreshold_pos_of_highBetaWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedThreshold_pos_of_highBetaWitness_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 : Real}
-- given
  (hd : 2 <= d)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) beta0) :
-- imply
  0 < beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedThreshold_pos_of_highBetaWitness d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 hq hhigh

/--
[weightedPhaseInfinite_singleOpen_measurable_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedPhaseInfinite_singleOpen_measurable_bound_eq
  {d N : Nat}
  {a : P}
  {q beta : Real}
  {eN : (boxGraph d N).edgeSet}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hA : MeasurableSet A) :
-- imply
  weightedOpenTolerance (betaParams (phaseJ a) beta (WiredBoxDifferential.boxActiveEdge d N eN)) q * ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real (setOpen (WiredBoxDifferential.boxActiveEdge d N eN) ⁻¹' A) <= ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real A := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedPhaseInfinite_singleOpen_measurable_bound d N phaseJ a hJ q beta hq hbeta eN A hA

/--
[div_q_le_weightedOpenTolerance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma div_q_le_weightedOpenTolerance_eq
  {p0 p q : Real}
-- given
  (hp0p : p0 <= p)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  p0 / q <= weightedOpenTolerance p q := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.div_q_le_weightedOpenTolerance hp0p hp hp1 hq

/--
[weightedUniformOpenConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedUniformOpenConstant_pos_eq
  {betaOne Jmin q : Real}
-- given
  (hbetaOne : 0 < betaOne)
  (hJmin : 0 < Jmin)
  (hq : 1 <= q) :
-- imply
  0 < weightedUniformOpenConstant betaOne Jmin q := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedUniformOpenConstant_pos hbetaOne hJmin hq

/--
[weightedUniformOpenConstant_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedUniformOpenConstant_le_eq
  {betaOne beta Jmin Jedge q : Real}
-- given
  (hbetaOne : 0 < betaOne)
  (hbeta : betaOne < beta)
  (hJmin : 0 < Jmin)
  (hJedge : Jmin <= Jedge)
  (hq : 1 <= q) :
-- imply
  weightedUniformOpenConstant betaOne Jmin q <= weightedOpenTolerance (1 - Real.exp (-(beta * Jedge))) q := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedUniformOpenConstant_le hbetaOne hbeta hJmin hJedge hq

/--
[forceOpenFinset_real_bound_of_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma forceOpenFinset_real_bound_of_single_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
  {F : Finset (Sym2 (Site d))}
  {c : Real}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hc : 0 <= c)
  (hone : forall e, e ∈ F -> forall A, MeasurableSet A -> c * mu.real (setOpen e ⁻¹' A) <= mu.real A)
  (hA : MeasurableSet A) :
-- imply
  c ^ F.card * mu.real (forceOpenFinset F ⁻¹' A) <= mu.real A := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.forceOpenFinset_real_bound_of_single mu F c hc hone A hA

/--
[weightedPhaseInfinite_forceOpen_box_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedPhaseInfinite_forceOpen_box_bound_eq
  {d n : Nat}
  {a : P}
  {Jmin : Real}
  {q betaOne beta : Real}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < phaseJ a e)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= phaseJ a e)
  (hq : 1 <= q)
  (hbetaOne : 0 < betaOne)
  (hbeta : betaOne < beta)
  (hA : MeasurableSet A) :
-- imply
  weightedUniformOpenConstant betaOne Jmin q ^ (boxEdges d n).card * ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) (hbetaOne.trans hbeta) : ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real (forceOpenFinset (boxEdges d n) ⁻¹' A) <= ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta (zero_lt_one.trans_le hq) (hbetaOne.trans hbeta) : ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real A := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedPhaseInfinite_forceOpen_box_bound d n phaseJ a hJ Jmin hJmin hJlo q betaOne beta hq hbetaOne hbeta A hA

/--
[uniformPhaseDensityComparison_of_threshold_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma uniformPhaseDensityComparison_of_threshold_pos_eq
  {d : Nat}
  [Empty.Finite P]
  [Nonempty P]
  {Jmin : Real}
  {q betaOne beta0 : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbetaOne : 0 < betaOne) :
-- imply
  UniformPhaseDensityComparison (weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq)) betaOne beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.uniformPhaseDensityComparison_of_threshold_pos d J Jmin hJmin hJlo phase phaseJ hsurj hcov q betaOne beta0 hq hbetaOne

/--
[individual_ge_uniform_mul_sum_div_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma individual_ge_uniform_mul_sum_div_card_eq
  [Fintype P]
  [Nonempty P]
  {betaC beta0 : Real}
-- given
  (theta : P -> Real -> Real)
  (hcomparison : UniformPhaseDensityComparison theta betaC beta0) :
-- imply
  exists kappa : Real, 0 < kappa /\ forall a beta, betaC < beta -> beta <= beta0 -> (kappa / Fintype.card P) * (∑ b : P, theta b beta) <= theta a beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.individual_ge_uniform_mul_sum_div_card theta betaC beta0 hcomparison

/--
[weightedIndividualPhase_meanField_lower_of_uniformComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedIndividualPhase_meanField_lower_of_uniformComparison_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta0 : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hne : (thresholdSet (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
  (hcomparison : UniformPhaseDensityComparison (weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq)) (beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) beta0) :
-- imply
  exists kappa : Real, 0 < kappa /\ forall a beta, beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta -> beta <= beta0 -> (kappa / Fintype.card P) * weightedPhaseSharpConstant d Jmin Jmax beta0 * (beta - beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) <= weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedIndividualPhase_meanField_lower_of_uniformComparison d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta0 hq hne hcomparison

/--
[weightedUniformPhaseDensityComparison_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedUniformPhaseDensityComparison_of_two_le_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q : Real}
-- given
  (hd : 2 <= d)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  exists beta0 : Real, UniformPhaseDensityComparison (weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq)) (beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) beta0 := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedUniformPhaseDensityComparison_of_two_le d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q hq

/--
[weightedIndividualPhase_meanField_lower_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedIndividualPhase_meanField_lower_of_two_le_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q : Real}
-- given
  (hd : 2 <= d)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  exists beta0 : Real, exists kappa : Real, 0 < kappa /\ forall a beta, beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta -> beta <= beta0 -> (kappa / Fintype.card P) * weightedPhaseSharpConstant d Jmin Jmax beta0 * (beta - beta1 (fun b n => Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) <= weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedIndividualPhase_meanField_lower_of_two_le d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q hq

/--
[weightedPhasePhysical_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedPhasePhysical_one_sub_lower_eq
  {d n : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q beta beta0 : Real}
  {a : P}
-- given
  (hn : 2 <= n)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  Real.exp (-(beta0 * Jmax)) ^ (2 * d) <= 1 - ((weightedPhaseFiniteMeasure d n phaseJ a (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e)) a) q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedPhasePhysical_one_sub_lower d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q beta beta0 hq hbeta hbeta0 a

/--
[prefactor_exp_decay_of_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma prefactor_exp_decay_of_one_sub_lower_eq
  {C epsilon rate : Real}
-- given
  (u : I -> Nat -> Real)
  (hC : 0 < C)
  (hepsilon : 0 < epsilon)
  (hepsilon1 : epsilon <= 1)
  (hrate : 0 < rate)
  (hu0 : forall i n, 2 <= n -> 0 <= u i n)
  (hgap : forall i n, 2 <= n -> epsilon <= 1 - u i n)
  (hdecay : forall i n, 2 <= n -> u i n <= C * Real.exp (-(rate * (n : Real)))) :
-- imply
  exists c : Real, 0 < c /\ forall i n, 2 <= n -> u i n <= Real.exp (-(c * (n : Real))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.prefactor_exp_decay_of_one_sub_lower u C epsilon rate hC hepsilon hepsilon1 hrate hu0 hgap hdecay

/--
[weightedPeriodicSharpness_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean)
-/
@[path]
private lemma weightedPeriodicSharpness_of_two_le_eq
  {d : Nat}
  [Fintype P]
  [Nonempty P]
  {Jmin Jmax : Real}
  {q : Real}
-- given
  (hd : 2 <= d)
  (J : Sym2 (Site d) -> Real)
  (hJmin : 0 < Jmin)
  (hJlo : forall e, Jmin <= J e)
  (hJhi : forall e, J e <= Jmax)
  (phase : Site d -> P)
  (phaseJ : P -> Sym2 (Site d) -> Real)
  (hsurj : Function.Surjective phase)
  (hcov : PhaseCovariant J phase phaseJ)
  (hq : 1 <= q) :
-- imply
  exists beta0 betaC kappa : Real, 0 < betaC /\ betaC < beta0 /\ 0 < kappa /\ (forall a : P, sSup (BetaCMatch.bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a)) = betaC) /\ (forall a beta, betaC < beta -> beta <= beta0 -> (kappa / Fintype.card P) * weightedPhaseSharpConstant d Jmin Jmax beta0 * (beta - betaC) <= weightedPhaseThetaProfile d phaseJ (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))) q (zero_lt_one.trans_le hq) a beta) /\ forall gamma, (hgamma : 0 < gamma) -> gamma < betaC -> exists c : Real, 0 < c /\ forall a : P, forall n : Nat, 2 <= n -> ((weightedPhaseFiniteMeasure d n phaseJ a (hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e)) a) q gamma (zero_lt_one.trans_le hq) hgamma : ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) <= Real.exp (-(c * (n : Real))) := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedPhasewiseMeanField.weightedPeriodicSharpness_of_two_le d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov q hq


-- created on 2026-10-23
