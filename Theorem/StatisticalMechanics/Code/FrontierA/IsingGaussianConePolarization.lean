/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.LinearAlgebra.Lagrange
open Filter Finset Polynomial Topology


namespace StatMech.FrontierA

theorem polynomial_eval_tendsto_zero_of_nodes
    (degree : Nat) (p : Nat -> Real[X])
    (hdegree : forall scale, (p scale).degree < (degree + 1 : Nat))
    (hnodes : forall i : Fin (degree + 1),
      Tendsto (fun scale => (p scale).eval ((i : Nat) : Real))
        atTop (nhds 0))
    (x : Real) :
    Tendsto (fun scale => (p scale).eval x) atTop (nhds 0) := by
  let nodes : Fin (degree + 1) -> Real := fun i => ((i : Nat) : Real)
  have hnodesInjective : Function.Injective nodes := by
    intro i j hij
    apply Fin.ext
    change (((i : Nat) : Real) = ((j : Nat) : Real)) at hij
    exact_mod_cast hij
  have heval (scale : Nat) :
      (p scale).eval x =
        Finset.sum Finset.univ (fun i : Fin (degree + 1) =>
          (p scale).eval (nodes i) *
            (Lagrange.basis univ nodes i).eval x) := by
    have hp : p scale =
        Lagrange.interpolate (Finset.univ : Finset (Fin (degree + 1))) nodes
          (fun i => (p scale).eval (nodes i)) :=
      Lagrange.eq_interpolate hnodesInjective.injOn (by
        simpa using hdegree scale)
    calc
      (p scale).eval x =
          (Lagrange.interpolate
            (Finset.univ : Finset (Fin (degree + 1))) nodes
            (fun i => (p scale).eval (nodes i))).eval x :=
        congrArg (fun q : Real[X] => q.eval x) hp
      _ = _ := by
        simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  have hsum : Tendsto
      (fun scale => Finset.sum Finset.univ (fun i : Fin (degree + 1) =>
        (p scale).eval (nodes i) *
          (Lagrange.basis univ nodes i).eval x))
      atTop (nhds 0) := by
    simpa only [zero_mul, Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset (Fin (degree + 1))) (fun i _ =>
        (hnodes i).mul_const ((Lagrange.basis univ nodes i).eval x))
  convert hsum using 1
  funext scale
  exact heval scale


end StatMech.FrontierA
