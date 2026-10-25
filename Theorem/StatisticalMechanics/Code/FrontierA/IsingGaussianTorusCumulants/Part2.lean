/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusScalingHandoff
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusCumulants
open Filter MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising StatMech.FrontierB

noncomputable section

variable {d k : Nat}


theorem integral_pow_projection_isingTorusScaledSmearedFieldLaw
    (beta c t : Real) (a : IsingDyadicTorus d k → Real)
    (order : Nat) :
    (∫ x, x ^ order
        ∂(((isingTorusFieldLaw d k beta
          (isingTorusScaledSmearedField c a)).map
            (InnerProductSpace.toDualMap Real Real t).continuous.measurable.aemeasurable) :
              Measure Real)) =
      (t * c) ^ order *
        finiteIsingWeightedRawMoment
          (isingTorusGraph d k) beta a order := by
  change (∫ x, x ^ order
      ∂Measure.map (InnerProductSpace.toDualMap Real Real t)
        (Measure.map (isingTorusScaledSmearedField c a)
          (isingTorusZeroFieldLaw (d := d) (k := k) beta : Measure _))) = _
  rw [MeasureTheory.integral_map
    (InnerProductSpace.toDualMap Real Real t).continuous.measurable.aemeasurable
    (by fun_prop)]
  rw [MeasureTheory.integral_map
    (Measurable.of_discrete :
      Measurable (isingTorusScaledSmearedField c a)).aemeasurable
    (by fun_prop)]
  simp only [InnerProductSpace.toDualMap_apply_apply, RCLike.inner_apply,
    conj_trivial, isingTorusScaledSmearedField]
  have hpoint : (fun x : ConfigSpace (IsingDyadicTorus d k) =>
      (c * isingTorusSmearedSpin a x * t) ^ order) =
      fun x => (t * c) ^ order * isingTorusSmearedSpin a x ^ order := by
    funext x
    rw [show c * isingTorusSmearedSpin a x * t =
      (t * c) * isingTorusSmearedSpin a x by ring, mul_pow]
  rw [hpoint, integral_const_mul,
    integral_pow_isingTorusSmearedSpin_eq_finiteIsingWeightedRawMoment]


theorem isingTorusScaledSmeared_hasScalarMomentCumulantRecurrence
    (d : Nat) (beta : Real) (c : Nat → Real)
    (a : (k : Nat) → IsingDyadicTorus d k → Real) (t : Real) :
    HasScalarMomentCumulantRecurrence
      (fun k order =>
        ∫ x, x ^ order
          ∂(((isingTorusFieldLaw d k beta
            (isingTorusScaledSmearedField (c k) (a k))).map
              (InnerProductSpace.toDualMap Real Real t).continuous.measurable.aemeasurable) :
                Measure Real))
      (fun k order =>
        isingTorusScaledSmearedCumulant beta (c k) t (a k) order) := by
  have hrec := hasScalarMomentCumulantRecurrence_cumulantsOfMoments
    (fun k order => (t * c k) ^ order *
      finiteIsingWeightedRawMoment
        (isingTorusGraph d k) beta (a k) order)
    (fun k => by
      simp [PhysicalIsing.finiteIsingWeightedRawMoment_zero])
  simpa only [isingTorusScaledSmearedCumulant,
    integral_pow_projection_isingTorusScaledSmearedFieldLaw] using hrec


theorem isingTorusScaledSmeared_newmanFourthCumulantControl
    (d : Nat) (beta : Real) (hbeta : 0 ≤ beta)
    (c : Nat → Real)
    (a : (k : Nat) → IsingDyadicTorus d k → Real)
    (ha : ∀ k x, 0 < a k x) (t : Real) :
    NewmanFourthCumulantControl
      (fun k order =>
        isingTorusScaledSmearedCumulant beta (c k) t (a k) order) := by
  let F : Nat → Complex → Complex := fun k z =>
    finiteIsingWeightedFieldPartition (isingTorusGraph d k) beta (a k)
      (((t * c k : Real) : Complex) * z)
  have hF : ∀ k, EvenHadamardFactorization (F k) := fun k =>
    (finiteIsingWeightedFieldPartition_factorization
      (isingTorusGraph d k) hbeta (a k) (ha k)).scaleArgument (t * c k)
  apply newmanFourthCumulantControl_of_eq_hadamardScalarCumulant F hF
  intro k order
  exact finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant
    (isingTorusGraph d k) beta (a k) (t * c k)
      (finiteIsingWeightedFieldPartition_factorization
        (isingTorusGraph d k) hbeta (a k) (ha k)) order


theorem finiteIsingWeighted_physical_newmanFourthCumulantControl_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Nat → Real) (hbeta : ∀ n, 0 ≤ beta n)
    (a : Nat → V → Real) (ha : ∀ n v, 0 < a n v) :
    NewmanFourthCumulantControl
      (fun n order => PhysicalIsing.finiteIsingWeightedCumulant
        G (beta n) (a n) order) :=
  finiteIsingWeighted_physical_newmanFourthCumulantControl G beta a
    (fun n => finiteIsingWeightedFieldPartition_factorization
      G (hbeta n) (a n) (ha n))

end
end StatMech.FrontierA
