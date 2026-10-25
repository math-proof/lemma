/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.CohomologyIsomorphismConcrete
open ContinuousAlternatingMap


namespace DeRhamConcrete

section CohomologyIsomorphism

variable {E_X E_U : Type*}
  [NormedAddCommGroup E_X] [NormedSpace ℝ E_X]
  [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]

namespace HasDeformationRetractConcrete

variable {i : E_X → E_U} {π : E_U → E_X}

/-- Pullback along the identity is the identity: $\mathrm{id}^*\omega = \omega$. -/
lemma pullbackForm_id {n : ℕ} (ω : DiffForm E n) :
    pullbackForm id ω = ω := by
  ext x v
  simp [pullbackForm, fderiv_id, ContinuousAlternatingMap.compContinuousLinearMap]

/-- The exterior derivative of the zero form is zero: $d 0 = 0$. -/
lemma extDeriv_zero_eq_zero {n : ℕ} :
    extDeriv (0 : DiffForm E n) = (0 : DiffForm E (n + 1)) := by
  funext x
  change ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (0 : E → E [⋀^Fin n]→L[ℝ] ℝ) x) = 0
  rw [show (0 : E → E [⋀^Fin n]→L[ℝ] ℝ) = Function.const E 0 from rfl]
  simp [ContinuousAlternatingMap.alternatizeUncurryFin, ContinuousLinearMap.map_zero]

/-- Any function out of a subsingleton normed space is smooth (it is constant). -/
lemma contDiff_of_subsingleton_domain {E' F : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Subsingleton E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E' → F) : ContDiff ℝ ⊤ f := by
  have : f = Function.const E' (f 0) := by
    ext x; have h : x = 0 := Subsingleton.elim x 0; subst h; rfl
  rw [this]; exact contDiff_const

end HasDeformationRetractConcrete
end CohomologyIsomorphism
end DeRhamConcrete
