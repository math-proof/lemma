/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization.Part4
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


namespace PhysicalIsing

theorem criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval
    (d n : Nat) (hd : 2 <= d)
    (positive direction : sctBox d n -> Real) (order : Nat) (r : Real) :
    (criticalFiniteBoxWeightedScaledCumulantLinePolynomial
      d n hd positive direction order).eval r =
      criticalFiniteBoxWeightedScaledCumulant d n hd
        (positive + r • direction) order := by
  unfold criticalFiniteBoxWeightedScaledCumulantLinePolynomial
    criticalFiniteBoxWeightedScaledCumulant
  rw [eval_mul, eval_C,
    finiteIsingWeightedCumulantLinePolynomial_eval,
    finiteIsingWeighted_scaledCumulants]

theorem criticalFiniteBoxWeightedScaledCumulantLinePolynomial_degree_lt
    (d n : Nat) (hd : 2 <= d)
    (positive direction : sctBox d n -> Real) (order : Nat) :
    (criticalFiniteBoxWeightedScaledCumulantLinePolynomial
      d n hd positive direction order).degree < (order + 1 : Nat) := by
  apply lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le ?_)
    (by exact_mod_cast Nat.lt_succ_self order)
  unfold criticalFiniteBoxWeightedScaledCumulantLinePolynomial
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C]
  simpa [finiteIsingWeightedCumulantLinePolynomial] using
    scalarCumulantLinePolynomial_natDegree_le
      (finiteIsingWeightedRawMomentLinePolynomial
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
          positive direction)
      (finiteIsingWeightedRawMomentLinePolynomial_natDegree_le
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
          positive direction) order


theorem criticalFiniteBoxWeightedScaledCumulant_tendsto_zero_of_nonnegative_line
    (d order : Nat) (hd : 2 <= d)
    (positive negative signed : (n : Nat) -> sctBox d n -> Real)
    (hsigned : forall n, signed n = positive n - negative n)
    (hnodes : forall i : Fin (order + 1),
      Tendsto
        (fun n => criticalFiniteBoxWeightedScaledCumulant d n hd
          (positive n + (((i : Nat) : Real) • negative n)) order)
        atTop (nhds 0)) :
    Tendsto
      (fun n => criticalFiniteBoxWeightedScaledCumulant
        d n hd (signed n) order) atTop (nhds 0) := by
  have hpoly := polynomial_eval_tendsto_zero_of_nodes order
    (fun n => criticalFiniteBoxWeightedScaledCumulantLinePolynomial
      d n hd (positive n) (negative n) order)
    (fun n => criticalFiniteBoxWeightedScaledCumulantLinePolynomial_degree_lt
      d n hd (positive n) (negative n) order)
    (fun i => by
      simpa only [criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval]
        using hnodes i) (-1)
  convert hpoly using 1
  funext n
  rw [criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval, hsigned n]
  simp only [neg_smul, one_smul]
  rw [sub_eq_add_neg]

end PhysicalIsing
end
end StatMech.FrontierA
