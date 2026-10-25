/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingReflectionKernel
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Mathlib.Analysis.Calculus.Taylor
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part2
open Finset Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising


variable {d k : Nat}


theorem iteratedDeriv_two_nonpos_of_global_max
    (f : Real → Real) (hf : ContDiff Real 2 f)
    (hmax : ∀ x, f x ≤ f 0) :
    iteratedDeriv 2 f 0 ≤ 0 := by
  have hm : IsLocalMax f 0 := Filter.Eventually.of_forall hmax
  have hd : deriv f 0 = 0 := hm.deriv_eq_zero
  have hpoly (x : Real) : taylorWithinEval f 2 Set.univ 0 x =
      f 0 + (iteratedDeriv 2 f 0 / 2) * x ^ 2 := by
    rw [taylorWithinEval_succ f 1, taylorWithinEval_succ f 0,
      taylor_within_zero_eval]
    simp [iteratedDerivWithin_univ, hd]
    ring
  have ht := Real.taylor_tendsto (f := f) (x₀ := 0) (n := 2)
    convex_univ (mem_univ 0) hf.contDiffOn
  simp only [hpoly, sub_zero] at ht
  have ht' : Tendsto (fun x =>
      (f x - (f 0 + iteratedDeriv 2 f 0 / 2 * x ^ 2)) / x ^ 2)
      (nhds 0) (nhds 0) := by simpa using ht
  have hadd := ht'.add
    (tendsto_const_nhds : Tendsto
      (fun _ : Real => iteratedDeriv 2 f 0 / 2)
      (nhds 0) (nhds (iteratedDeriv 2 f 0 / 2)))
  have hadd' : Tendsto (fun x =>
      (f x - (f 0 + iteratedDeriv 2 f 0 / 2 * x ^ 2)) / x ^ 2 +
        iteratedDeriv 2 f 0 / 2) (nhds 0)
      (nhds (iteratedDeriv 2 f 0 / 2)) := by simpa using hadd
  have hratio : Tendsto (fun x : Real => (f x - f 0) / x ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (iteratedDeriv 2 f 0 / 2)) := by
    apply hadd'.mono_left inf_le_left |>.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    field_simp
    ring
  have hle : iteratedDeriv 2 f 0 / 2 ≤ 0 :=
    le_of_tendsto hratio (Filter.Eventually.of_forall (fun x =>
      div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hmax x)) (sq_nonneg x)))
  linarith

end StatMech.FrontierA
