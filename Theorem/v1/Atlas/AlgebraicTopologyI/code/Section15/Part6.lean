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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part7
open Topology


namespace SphereInfty

/-- The affine combination `v_id_T p` is finitely supported, since both
$x$ and $T x$ are. -/
lemma v_id_T_mem_RInfty (p : I × Sphere) : v_id_T p ∈ RInfty :=
  RInfty.add_mem (RInfty.smul_mem _ p.2.mem_RInfty)
    (RInfty.smul_mem _ (T_mem_RInfty p.2.mem_RInfty))

/-- The straight-line family `v_id_T` depends continuously on $(t, x)$. -/
lemma continuous_v_id_T : Continuous v_id_T := by
  unfold v_id_T
  exact ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_T.comp (continuous_subtype_val.comp continuous_snd)))

/-- The straight-line family `v_id_T` never vanishes, so normalization is
well-defined throughout. -/
lemma v_id_T_ne_zero (p : I × Sphere) : v_id_T p ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt (norm_affine_id_T_pos _ (norm_eq_one p.2) _ p.1.2.1 p.1.2.2))


end SphereInfty
