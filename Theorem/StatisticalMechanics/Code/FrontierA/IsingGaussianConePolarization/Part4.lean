/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.LinearAlgebra.Lagrange
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part3
open Filter Finset Polynomial Topology


namespace StatMech.FrontierA

theorem finiteWeightedCumulantLinePolynomial_eval
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) (r : Real) :
    (finiteWeightedCumulantLinePolynomial order ursell positive negative).eval r =
      finiteWeightedCumulant order ursell (positive + r • negative) := by
  classical
  unfold finiteWeightedCumulantLinePolynomial finiteWeightedCumulant
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x _
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [eval_add, eval_C, eval_mul, eval_X, Pi.add_apply,
    Pi.smul_apply]
  ring

theorem finiteWeightedCumulantLinePolynomial_natDegree_le
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) :
    (finiteWeightedCumulantLinePolynomial order ursell positive negative).natDegree <=
      order := by
  classical
  unfold finiteWeightedCumulantLinePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  refine Polynomial.natDegree_mul_le.trans ?_
  have hprod :
      (∏ i : Fin order,
        (C (positive (x i)) + C (negative (x i)) * X)).natDegree <= order := by
    calc
      _ <= ∑ i : Fin order,
          (C (positive (x i)) + C (negative (x i)) * X).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ <= ∑ _i : Fin order, 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le (by simp) ((Polynomial.natDegree_mul_le).trans (by simp)))
      _ = order := by simp
  simpa using hprod

theorem finiteWeightedCumulantLinePolynomial_degree_lt
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) :
    (finiteWeightedCumulantLinePolynomial order ursell positive negative).degree <
      (order + 1 : Nat) := by
  exact lt_of_le_of_lt
    (Polynomial.degree_le_of_natDegree_le
      (finiteWeightedCumulantLinePolynomial_natDegree_le
        order ursell positive negative))
    (by exact_mod_cast Nat.lt_succ_self order)


theorem signedCumulant_tendsto_zero_of_nonnegative_line
    {E : Type*} [AddCommGroup E] [Module Real E]
    (order : Nat) (cumulant : Nat -> E -> Real)
    (linePolynomial : Nat -> E -> E -> Real[X])
    (hdegree : forall scale positive negative,
      (linePolynomial scale positive negative).degree < (order + 1 : Nat))
    (heval : forall scale positive negative r,
      (linePolynomial scale positive negative).eval r =
        cumulant scale (positive + r • negative))
    (positive negative signed : E)
    (hsigned : signed = positive - negative)
    (hnodes : forall i : Fin (order + 1),
      Tendsto
        (fun scale => cumulant scale
          (positive + (((i : Nat) : Real) • negative)))
        atTop (nhds 0)) :
    Tendsto (fun scale => cumulant scale signed) atTop (nhds 0) := by
  have hpoly := polynomial_eval_tendsto_zero_of_nodes order
    (fun scale => linePolynomial scale positive negative)
    (fun scale => hdegree scale positive negative)
    (fun i => by simpa only [heval] using hnodes i) (-1)
  convert hpoly using 1
  funext scale
  rw [heval]
  simp only [neg_smul, one_smul, sub_eq_add_neg, hsigned]


theorem finiteWeightedCumulant_tendsto_zero_of_nonnegative_line
    {V : Type*} [Fintype V]
    (order : Nat) (ursell : Nat -> (Fin order -> V) -> Real)
    (positive negative signed : V -> Real)
    (hsigned : signed = positive - negative)
    (hnodes : forall i : Fin (order + 1),
      Tendsto
        (fun scale => finiteWeightedCumulant order (ursell scale)
          (positive + (((i : Nat) : Real) • negative)))
        atTop (nhds 0)) :
    Tendsto
      (fun scale => finiteWeightedCumulant order (ursell scale) signed)
      atTop (nhds 0) := by
  apply signedCumulant_tendsto_zero_of_nonnegative_line order
    (fun scale a => finiteWeightedCumulant order (ursell scale) a)
    (fun scale => finiteWeightedCumulantLinePolynomial order (ursell scale))
    (fun scale positive negative =>
      finiteWeightedCumulantLinePolynomial_degree_lt
        order (ursell scale) positive negative)
    (fun scale positive negative r =>
      finiteWeightedCumulantLinePolynomial_eval
        order (ursell scale) positive negative r)
    positive negative signed hsigned hnodes

end StatMech.FrontierA
