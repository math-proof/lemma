import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants
open Filter Finset Topology StatMech StatMech.FrontierA StatMech.FrontierA.PhysicalIsing


/--
[scalarCumulantsOfMoments_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_zero_eq
-- given
  (moments : Nat -> Real) :
-- imply
  scalarCumulantsOfMoments moments 0 = 0 := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_zero moments

/--
[scalarCumulantsOfMoments_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_succ_eq
  {n : Nat}
-- given
  (moments : Nat -> Real) :
-- imply
  scalarCumulantsOfMoments moments (n + 1) = moments (n + 1) - ∑ k : Fin n, (n.choose k : Real) * scalarCumulantsOfMoments moments (k + 1) * moments (n - k) := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_succ moments n

/--
[hasScalarMomentCumulantRecurrence_cumulantsOfMoments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma hasScalarMomentCumulantRecurrence_cumulantsOfMoments_eq
-- given
  (moments : Nat -> Nat -> Real)
  (hmomentZero : forall scale, moments scale 0 = 1) :
-- imply
  HasScalarMomentCumulantRecurrence moments (fun scale => scalarCumulantsOfMoments (moments scale)) := by
-- proof
  apply StatMech.FrontierA.hasScalarMomentCumulantRecurrence_cumulantsOfMoments moments hmomentZero

/--
[scalarCumulantsOfMoments_eq_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_eq_of_recurrence_eq
-- given
  (moments cumulants : Nat -> Real)
  (hmomentZero : moments 0 = 1)
  (hcumulantZero : cumulants 0 = 0)
  (hrecurrence : forall order, moments (order + 1) = ∑ k ∈ Finset.range (order + 1), (order.choose k : Real) * cumulants (k + 1) * moments (order - k)) :
-- imply
  forall order, scalarCumulantsOfMoments moments order = cumulants order := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_eq_of_recurrence moments cumulants hmomentZero hcumulantZero hrecurrence

/--
[scalarCumulantsOfMoments_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_one_eq
-- given
  (moments : Nat -> Real) :
-- imply
  scalarCumulantsOfMoments moments 1 = moments 1 := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_one moments

/--
[scalarCumulantsOfMoments_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_two_eq
-- given
  (moments : Nat -> Real) :
-- imply
  scalarCumulantsOfMoments moments 2 = moments 2 - moments 1 ^ 2 := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_two moments

/--
[scalarCumulantsOfMoments_three_of_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_three_of_centered_eq
-- given
  (moments : Nat -> Real)
  (hone : moments 1 = 0)
  (hthree : moments 3 = 0) :
-- imply
  scalarCumulantsOfMoments moments 3 = 0 := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_three_of_centered moments hone hthree

/--
[scalarCumulantsOfMoments_four_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_four_of_symmetric_eq
-- given
  (moments : Nat -> Real)
  (hone : moments 1 = 0)
  (hthree : moments 3 = 0) :
-- imply
  scalarCumulantsOfMoments moments 4 = scalarFourthCumulant (moments 4) (moments 2) := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_four_of_symmetric moments hone hthree

/--
[scalarCumulantsOfMoments_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_odd_eq
-- given
  (moments : Nat -> Real)
  (hmoments : forall order, Odd order -> moments order = 0) :
-- imply
  forall order, Odd order -> scalarCumulantsOfMoments moments order = 0 := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_odd moments hmoments

/--
[scalarCumulantsOfMoments_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma scalarCumulantsOfMoments_scale_eq
  {c : Real}
-- given
  (moments : Nat -> Real) :
-- imply
  forall order, scalarCumulantsOfMoments (fun m => c ^ m * moments m) order = c ^ order * scalarCumulantsOfMoments moments order := by
-- proof
  apply StatMech.FrontierA.scalarCumulantsOfMoments_scale moments c

/--
[iteratedDeriv_zero_of_even_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_zero_of_even_of_odd_eq
  {order : Nat}
-- given
  (F : Complex -> Complex)
  (heven : forall z, F (-z) = F z)
  (horder : Odd order) :
-- imply
  iteratedDeriv order F 0 = 0 := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_zero_of_even_of_odd F heven order horder

/--
[finiteIsingWeightedRawMoment_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedRawMoment G beta a 0 = 1 := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeightedRawMoment_zero beta a

/--
[finiteIsingWeightedRawMoment_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_odd_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (a : V -> Real)
  (horder : Odd order) :
-- imply
  finiteIsingWeightedRawMoment G beta a order = 0 := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeightedRawMoment_odd beta a order horder

/--
[finiteIsingWeighted_hasScalarMomentCumulantRecurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeighted_hasScalarMomentCumulantRecurrence_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (beta : Nat -> Real)
  (a : (scale : Nat) -> V -> Real) :
-- imply
  HasScalarMomentCumulantRecurrence (fun scale => finiteIsingWeightedRawMoment G (beta scale) (a scale)) (fun scale => finiteIsingWeightedCumulant G (beta scale) (a scale)) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeighted_hasScalarMomentCumulantRecurrence beta a

/--
[finiteIsingWeightedCumulant_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedCumulant_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedCumulant G beta a 0 = 0 := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeightedCumulant_zero beta a

/--
[finiteIsingWeightedCumulant_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedCumulant_odd_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (a : V -> Real)
  (horder : Odd order) :
-- imply
  finiteIsingWeightedCumulant G beta a order = 0 := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeightedCumulant_odd beta a order horder

/--
[finiteIsingWeighted_scaledCumulants](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeighted_scaledCumulants_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {c : Real}
  {order : Nat}
-- given
  (a : V -> Real) :
-- imply
  scalarCumulantsOfMoments (fun m => c ^ m * finiteIsingWeightedRawMoment G beta a m) order = c ^ order * finiteIsingWeightedCumulant G beta a order := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeighted_scaledCumulants beta a c order

/--
[finiteIsingWeightedCumulant_two_eq_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedCumulant_two_eq_parity_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedCumulant G beta a 2 = finiteWeightedParitySecondMoment G beta (fun _ => 1) a := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeightedCumulant_two_eq_parity beta a

/--
[finiteIsingWeightedCumulant_four_eq_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedCumulant_four_eq_parity_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
-- given
  (a : V -> Real) :
-- imply
  finiteIsingWeightedCumulant G beta a 4 = finiteWeightedParityFourthCumulant G beta (fun _ => 1) a := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.finiteIsingWeightedCumulant_four_eq_parity beta a

/--
[criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
  {c : Real}
-- given
  (a : sctBox d n -> Real)
  (hc : c ^ 4 = 1 / (2 * (Fintype.card (sctBox d n) : Real) * criticalFreeBoxSusceptibility d (2 * n) ^ 2 * ((2 * n + 1 : Nat) : Real) ^ d)) :
-- imply
  criticalFiniteBoxWeightedNormalizedFourthCumulant d n a = scalarCumulantsOfMoments (fun order => c ^ order * finiteIsingWeightedRawMoment (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a order) 4 := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled d n a c hc

/--
[exists_criticalFiniteBoxWeightedFourthScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma exists_criticalFiniteBoxWeightedFourthScale_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  ∃ c : Real, 0 < c ∧ c ^ 4 = 1 / (2 * (Fintype.card (sctBox d n) : Real) * criticalFreeBoxSusceptibility d (2 * n) ^ 2 * ((2 * n + 1 : Nat) : Real) ^ d) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.exists_criticalFiniteBoxWeightedFourthScale d n hd

/--
[criticalFiniteBoxWeightedFourthScale_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedFourthScale_pos_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  0 < criticalFiniteBoxWeightedFourthScale d n hd := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedFourthScale_pos d n hd

/--
[criticalFiniteBoxWeightedFourthScale_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedFourthScale_pow_four_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  criticalFiniteBoxWeightedFourthScale d n hd ^ 4 = 1 / (2 * (Fintype.card (sctBox d n) : Real) * criticalFreeBoxSusceptibility d (2 * n) ^ 2 * ((2 * n + 1 : Nat) : Real) ^ d) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedFourthScale_pow_four d n hd

/--
[exists_criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma exists_criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
-- given
  (hd : 2 <= d)
  (a : sctBox d n -> Real) :
-- imply
  ∃ c : Real, 0 < c ∧ criticalFiniteBoxWeightedNormalizedFourthCumulant d n a = scalarCumulantsOfMoments (fun order => c ^ order * finiteIsingWeightedRawMoment (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a order) 4 := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.exists_criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled d n hd a

/--
[criticalFiniteBoxWeightedScaledFourthCumulant_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaledFourthCumulant_tendsto_zero_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
-- given
  (hd : 4 < d)
  (a : (n : Nat) -> sctBox d n -> Real)
  (ha0 : forall n i, 0 <= a n i)
  (ha1 : forall n i, a n i <= 1) :
-- imply
  Tendsto (fun n => scalarCumulantsOfMoments (fun order => criticalFiniteBoxWeightedFourthScale d n (by omega) ^ order * finiteIsingWeightedRawMoment (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) order) 4) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedScaledFourthCumulant_tendsto_zero d hd a ha0 ha1

/--
[criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
-- given
  (hd : 4 < d)
  (a : (n : Nat) -> sctBox d n -> Real)
  (ha0 : forall n i, 0 <= a n i)
  (ha1 : forall n i, a n i <= 1) :
-- imply
  Tendsto (fun n => criticalFiniteBoxWeightedScaledCumulant d n (by omega) (a n) 4) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero d hd a ha0 ha1


-- created on 2026-10-23
