/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants.Part3
open Filter
open scoped BigOperators Complex Nat


namespace StatMech.FrontierA

noncomputable section

theorem newmanFourthCumulantControl_of_evenHadamardFactorizations
    (F : Nat → Complex → Complex)
    (hF : ∀ scale, EvenHadamardFactorization (F scale)) :
    NewmanFourthCumulantControl
      (fun scale order => hadamardScalarCumulant (F scale) order) :=
  (newmanRootCumulantRepresentation_of_evenHadamardFactorizations F hF).newmanFourthCumulantControl


theorem newmanFourthCumulantControl_of_eq_hadamardScalarCumulant
    (F : Nat -> Complex -> Complex)
    (hF : forall scale, EvenHadamardFactorization (F scale))
    (cumulants : Nat -> Nat -> Real)
    (heq : forall scale order,
      cumulants scale order = hadamardScalarCumulant (F scale) order) :
    NewmanFourthCumulantControl cumulants := by
  have hcontrol :=
    newmanFourthCumulantControl_of_evenHadamardFactorizations F hF
  have hfun : cumulants =
      fun scale order => hadamardScalarCumulant (F scale) order := by
    funext scale order
    exact heq scale order
  rw [hfun]
  exact hcontrol

section FiniteIsingNewman

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteIsingWeightedRawMoment_hadamard_recurrence
    (beta : Real) (a : V -> Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    (order : Nat) :
    finiteIsingWeightedRawMoment G beta a (order + 1) =
      ∑ k ∈ Finset.range (order + 1),
        (order.choose k : Real) *
          hadamardScalarCumulant
            (finiteIsingWeightedFieldPartition G beta a) (k + 1) *
          finiteIsingWeightedRawMoment G beta a (order - k) := by
  let F := finiteIsingWeightedFieldPartition G beta a
  have hanalytic : AnalyticAt Complex F 0 :=
    finiteIsingWeightedFieldPartition_analyticOnNhd G beta a 0 (by simp)
  have hzero : F 0 ≠ 0 := Complex.ne_zero_of_re_pos
    (finiteIsingWeightedFieldPartition_zero_re_pos G beta a)
  have hmoment (m : Nat) :
      iteratedDeriv m F 0 / F 0 =
        (finiteIsingWeightedRawMoment G beta a m : Complex) := by
    have h :=
      iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment
        G beta a m
    unfold finiteIsingWeightedMomentGeneratingFunction at h
    rw [iteratedDeriv_div_const] at h
    exact h
  have hrec := normalizedIteratedDeriv_logDeriv_recurrence
    F hanalytic hzero order
  dsimp [F] at hrec hmoment
  rw [hmoment (order + 1)] at hrec
  simp_rw [hF.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant] at hrec
  simp_rw [hmoment] at hrec
  exact_mod_cast hrec


theorem finiteIsingWeightedCumulant_eq_hadamardScalarCumulant
    (beta : Real) (a : V -> Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    (order : Nat) :
    PhysicalIsing.finiteIsingWeightedCumulant G beta a order =
      hadamardScalarCumulant
        (finiteIsingWeightedFieldPartition G beta a) order := by
  unfold PhysicalIsing.finiteIsingWeightedCumulant
  apply scalarCumulantsOfMoments_eq_of_recurrence
  · exact PhysicalIsing.finiteIsingWeightedRawMoment_zero G beta a
  · exact hadamardScalarCumulant_zero _
  · exact finiteIsingWeightedRawMoment_hadamard_recurrence G beta a hF


theorem finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant
    (beta : Real) (a : V -> Real) (c : Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    (order : Nat) :
    scalarCumulantsOfMoments
        (fun m => c ^ m * finiteIsingWeightedRawMoment G beta a m) order =
      hadamardScalarCumulant
        (fun z => finiteIsingWeightedFieldPartition G beta a
          ((c : Complex) * z)) order := by
  let baseF := finiteIsingWeightedFieldPartition G beta a
  let scaledF : Complex -> Complex := fun z => baseF ((c : Complex) * z)
  have hscaled : EvenHadamardFactorization scaledF := hF.scaleArgument c
  have hbaseAnalytic : AnalyticOnNhd Complex baseF Set.univ :=
    finiteIsingWeightedFieldPartition_analyticOnNhd G beta a
  have hscaledAnalytic : AnalyticAt Complex scaledF 0 := by
    dsimp [scaledF]
    exact (hbaseAnalytic ((c : Complex) * 0) (by simp)).comp'
      (by fun_prop)
  have hzero : scaledF 0 ≠ 0 := by
    dsimp [scaledF, baseF]
    simpa using Complex.ne_zero_of_re_pos
      (finiteIsingWeightedFieldPartition_zero_re_pos G beta a)
  have hbaseMoment (m : Nat) :
      iteratedDeriv m baseF 0 / baseF 0 =
        (finiteIsingWeightedRawMoment G beta a m : Complex) := by
    have h :=
      iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment
        G beta a m
    unfold finiteIsingWeightedMomentGeneratingFunction at h
    rw [iteratedDeriv_div_const] at h
    exact h
  have hscaledMoment (m : Nat) :
      iteratedDeriv m scaledF 0 / scaledF 0 =
        (c ^ m * finiteIsingWeightedRawMoment G beta a m : Real) := by
    have hcomp := congrFun
      (iteratedDeriv_comp_const_mul
        (n := m) (f := baseF) (hbaseAnalytic.contDiff) (c : Complex)) 0
    dsimp [scaledF] at hcomp ⊢
    rw [hcomp, mul_zero]
    calc
      (c : Complex) ^ m * iteratedDeriv m baseF 0 / baseF 0 =
          (c : Complex) ^ m * (iteratedDeriv m baseF 0 / baseF 0) := by ring
      _ = (c : Complex) ^ m *
          (finiteIsingWeightedRawMoment G beta a m : Complex) := by
        rw [hbaseMoment]
      _ = (c ^ m * finiteIsingWeightedRawMoment G beta a m : Real) := by
        push_cast
        rfl
  apply scalarCumulantsOfMoments_eq_of_recurrence
  · simp [PhysicalIsing.finiteIsingWeightedRawMoment_zero G beta a]
  · exact hadamardScalarCumulant_zero _
  · intro n
    have hrec := normalizedIteratedDeriv_logDeriv_recurrence
      scaledF hscaledAnalytic hzero n
    rw [hscaledMoment (n + 1)] at hrec
    simp_rw [hscaled.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant,
      hscaledMoment] at hrec
    exact_mod_cast hrec


theorem finiteIsingWeighted_newmanFourthCumulantControl
    (beta : Nat → Real) (a : Nat → V → Real)
    (hF : ∀ scale,
      FiniteIsingWeightedHadamardFactorization (G := G)
        (beta scale) (a scale)) :
    NewmanFourthCumulantControl
      (fun scale order => hadamardScalarCumulant
        (finiteIsingWeightedFieldPartition G (beta scale) (a scale)) order) :=
  newmanFourthCumulantControl_of_evenHadamardFactorizations
    (fun scale => finiteIsingWeightedFieldPartition G
      (beta scale) (a scale)) hF


theorem finiteIsingWeighted_physical_newmanFourthCumulantControl
    (beta : Nat -> Real) (a : Nat -> V -> Real)
    (hF : forall scale,
      FiniteIsingWeightedHadamardFactorization (G := G)
        (beta scale) (a scale)) :
    NewmanFourthCumulantControl
      (fun scale order =>
        PhysicalIsing.finiteIsingWeightedCumulant
          G (beta scale) (a scale) order) := by
  have hcontrol := finiteIsingWeighted_newmanFourthCumulantControl G beta a hF
  have heq :
      (fun scale order =>
        PhysicalIsing.finiteIsingWeightedCumulant
          G (beta scale) (a scale) order) =
      (fun scale order => hadamardScalarCumulant
        (finiteIsingWeightedFieldPartition G (beta scale) (a scale)) order) := by
    funext scale order
    exact finiteIsingWeightedCumulant_eq_hadamardScalarCumulant
      G (beta scale) (a scale) (hF scale) order
  rw [heq]
  exact hcontrol

end FiniteIsingNewman

section CriticalFiniteBoxes

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB


theorem criticalFiniteBoxWeighted_physical_newmanFourthCumulantControl
    (d : Nat) (a : (n : Nat) -> sctBox d n -> Real)
    (hF : forall n,
      FiniteIsingWeightedHadamardFactorization
        (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)) :
    NewmanFourthCumulantControl
      (fun n order => PhysicalIsing.finiteIsingWeightedCumulant
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) order) := by
  let F : Nat -> Complex -> Complex := fun n =>
    finiteIsingWeightedFieldPartition
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)
  apply newmanFourthCumulantControl_of_eq_hadamardScalarCumulant F hF
  intro n order
  exact finiteIsingWeightedCumulant_eq_hadamardScalarCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) (hF n) order


theorem criticalFiniteBoxWeightedScaled_newmanFourthCumulantControl
    (d : Nat) (hd : 2 <= d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (hF : forall n,
      FiniteIsingWeightedHadamardFactorization
        (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)) :
    NewmanFourthCumulantControl
      (fun n order => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
        d n hd (a n) order) := by
  let c : Nat -> Real := fun n =>
    PhysicalIsing.criticalFiniteBoxWeightedFourthScale d n hd
  let F : Nat -> Complex -> Complex := fun n z =>
    finiteIsingWeightedFieldPartition
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)
        ((c n : Complex) * z)
  have hscaled : forall n, EvenHadamardFactorization (F n) := fun n =>
    (hF n).scaleArgument (c n)
  apply newmanFourthCumulantControl_of_eq_hadamardScalarCumulant F hscaled
  intro n order
  unfold PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
  exact finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) (c n)
      (hF n) order


theorem criticalFiniteBoxWeightedScaled_cumulantLimits
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1)
    (hF : forall n,
      FiniteIsingWeightedHadamardFactorization
        (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n))
    (variance : Real)
    (hvariance : Tendsto
      (fun n => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
        d n (by omega) (a n) 2) atTop (nhds variance)) :
    forall order,
      Tendsto
        (fun n => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
          d n (by omega) (a n) order)
        atTop (nhds (scalarGaussianCumulant variance order)) := by
  apply cumulantLimits_of_newmanFourthControl _ variance
    (criticalFiniteBoxWeightedScaled_newmanFourthCumulantControl
      d (by omega) a hF) hvariance
  exact PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero
    d hd a ha0 ha1

end CriticalFiniteBoxes
end
end StatMech.FrontierA
