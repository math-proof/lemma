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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part8
open Topology


namespace SphereInfty

/-- The straight-line family `v_T_e1` is finitely supported. -/
lemma v_T_e1_mem_RInfty (p : I × Sphere) : v_T_e1 p ∈ RInfty :=
  RInfty.add_mem (RInfty.smul_mem _ (T_mem_RInfty p.2.mem_RInfty))
    (RInfty.smul_mem _ e1_mem_RInfty)

/-- The straight-line family `v_T_e1` depends continuously on $(t, x)$. -/
lemma continuous_v_T_e1 : Continuous v_T_e1 := by
  unfold v_T_e1
  exact ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_T.comp (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_const)

/-- The straight-line family `v_T_e1` never vanishes. -/
lemma v_T_e1_ne_zero (p : I × Sphere) : v_T_e1 p ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt (norm_affine_T_e1_pos _ (norm_eq_one p.2) _ p.1.2.1 p.1.2.2))

end SphereInfty
