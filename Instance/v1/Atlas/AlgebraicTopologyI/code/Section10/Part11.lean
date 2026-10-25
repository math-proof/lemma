/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part16
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

/-- `S^0` is finite (it is just the two-point set `{-1, +1}`). -/
instance sphere_zero_finite : Empty.Finite (Sphere 0) := by
  show Empty.Finite ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
  rw [Set.finite_coe_iff]
  let p1 : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ))
  let p2 : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ))
  apply Set.Finite.subset (Set.Finite.insert p1 (Set.finite_singleton p2))
  intro x hx
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hn := EuclideanSpace.norm_eq x
  rw [hx] at hn
  simp only [Fin.sum_univ_one] at hn
  rw [Real.sqrt_sq (norm_nonneg _)] at hn
  have habsx : x.ofLp 0 = 1 ∨ x.ofLp 0 = -1 := by
    rw [Real.norm_eq_abs] at hn
    exact abs_eq (by norm_num : (1 : ℝ) ≥ 0) |>.mp hn.symm
  rcases habsx with h | h
  · left; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p1]
  · right; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p2]

/-- `S^0` is totally disconnected (discrete two-point space). -/
instance sphere_zero_totallyDisconnected : TotallyDisconnectedSpace (Sphere 0) := by
  haveI : T1Space (Sphere 0) := by
    show T1Space ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    infer_instance
  haveI : DiscreteTopology (Sphere 0) := Finite.instDiscreteTopology
  infer_instance

end SphereHomology
