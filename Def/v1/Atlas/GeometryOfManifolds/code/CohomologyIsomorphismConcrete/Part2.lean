/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Theorem.v1.Atlas.GeometryOfManifolds.code.CohomologyIsomorphismConcrete
open ContinuousAlternatingMap


namespace DeRhamConcrete

section CohomologyIsomorphism

variable {E_X E_U : Type*}
  [NormedAddCommGroup E_X] [NormedSpace ℝ E_X]
  [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]

namespace HasDeformationRetractConcrete

variable {i : E_X → E_U} {π : E_U → E_X}

/-- The trivial deformation retract instance on a subsingleton (e.g., a point), with $K \equiv 0$. -/
noncomputable def DeRhamConcrete.HasDeformationRetractConcrete.ofSubsingleton
    (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Subsingleton E'] :
    HasDeformationRetractConcrete (id : E' → E') (id : E' → E') where
  smooth_i := contDiff_id
  smooth_π := contDiff_id
  retraction := fun ω => by rw [pullbackForm_id, pullbackForm_id]
  K := fun _ => 0
  K_smul := fun r β => by simp
  homotopy_formula := fun {p} β => by
    simp only [pullbackForm_id, sub_self]
    rw [extDeriv_zero_eq_zero]
    simp
  K_vanishes := fun _ => by
    ext x v; simp [pullbackForm]
  deg0_injectivity := fun β _ h => by
    rw [pullbackForm_id] at h; exact h
  smooth_forms_U := fun ω => contDiff_of_subsingleton_domain ω

end HasDeformationRetractConcrete
end CohomologyIsomorphism
end DeRhamConcrete
