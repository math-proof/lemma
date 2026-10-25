/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.UnitInterval
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section15.Part7
open Topology


namespace SphereInfty

/-- The constant continuous map from $S^{\infty}$ to itself sending every point
to the basepoint $e_1$. -/
def constE1 : C(Sphere, Sphere) :=
  ContinuousMap.const _ ⟨e1, e1_mem_sphere_set⟩


/-- A homotopy on $S^{\infty}$ from the shift map $T$ to the identity, obtained
by normalizing the straight-line family `v_id_T`. -/
def homotopy_T_to_id : ContinuousMap.Homotopy TOnSphere (ContinuousMap.id Sphere) where
  toFun p := normalizeToSphere (v_id_T p) (v_id_T_ne_zero p) (v_id_T_mem_RInfty p)
  continuous_toFun :=
    (continuous_normalize_comp v_id_T continuous_v_id_T v_id_T_ne_zero).subtype_mk _
  map_zero_left := by
    intro x; apply Subtype.ext
    simp only [v_id_T, Set.Icc.coe_zero, zero_smul, zero_add, sub_zero, one_smul,
      normalizeToSphere, TOnSphere, ContinuousMap.coe_mk]
    have hT : ‖T (x.1 : l2)‖ = 1 := by rw [T_norm]; exact norm_eq_one x
    simp [hT]
  map_one_left := by
    intro x; apply Subtype.ext
    simp only [v_id_T, Set.Icc.coe_one, one_smul, sub_self, zero_smul, add_zero,
      normalizeToSphere, ContinuousMap.id_apply]
    simp [norm_eq_one x]


/-- A homotopy on $S^{\infty}$ from the constant map at $e_1$ to the shift map
$T$, obtained by normalizing the straight-line family `v_T_e1`. -/
def homotopy_e1_to_T : ContinuousMap.Homotopy constE1 TOnSphere where
  toFun p := normalizeToSphere (v_T_e1 p) (v_T_e1_ne_zero p) (v_T_e1_mem_RInfty p)
  continuous_toFun :=
    (continuous_normalize_comp v_T_e1 continuous_v_T_e1 v_T_e1_ne_zero).subtype_mk _
  map_zero_left := by
    intro x; apply Subtype.ext
    simp only [v_T_e1, Set.Icc.coe_zero, zero_smul, zero_add, sub_zero, one_smul,
      normalizeToSphere, constE1, ContinuousMap.const_apply]
    simp [e1_norm]
  map_one_left := by
    intro x; apply Subtype.ext
    simp only [v_T_e1, Set.Icc.coe_one, one_smul, sub_self, zero_smul, add_zero,
      normalizeToSphere, TOnSphere, ContinuousMap.coe_mk]
    have hT : ‖T (x.1 : l2)‖ = 1 := by rw [T_norm]; exact norm_eq_one x
    simp [hT]


end SphereInfty
