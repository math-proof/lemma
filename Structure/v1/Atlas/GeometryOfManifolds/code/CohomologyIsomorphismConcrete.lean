/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.CohomologyIsomorphismConcrete
open ContinuousAlternatingMap


namespace DeRhamConcrete

section CohomologyIsomorphism

variable {E_X E_U : Type*}
  [NormedAddCommGroup E_X] [NormedSpace ℝ E_X]
  [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]

/-- Concrete deformation retract data $i : X \hookrightarrow U$ and $\pi : U \to X$ with a chain homotopy operator $K$ satisfying $dK + Kd = \mathrm{id} - \pi^* i^*$, used to prove $i^* : H^*(U) \xrightarrow{\sim} H^*(X)$. -/
structure HasDeformationRetractConcrete
    (i : E_X → E_U) (π : E_U → E_X) where
  smooth_i : ContDiff ℝ ⊤ i
  smooth_π : ContDiff ℝ ⊤ π
  retraction : ∀ {n : ℕ} (ω : DiffForm E_X n),
    pullbackForm i (pullbackForm π ω) = ω
  K : ∀ {p : ℕ}, DiffForm E_U (p + 1) → DiffForm E_U p
  K_smul : ∀ {p : ℕ} (r : ℝ) (β : DiffForm E_U (p + 1)),
    K (r • β) = r • K β
  homotopy_formula : ∀ {p : ℕ} (β : DiffForm E_U (p + 1)),
    extDeriv (K β) + K (extDeriv β) = β - pullbackForm π (pullbackForm i β)
  K_vanishes : ∀ {p : ℕ} (β : DiffForm E_U (p + 1)),
    pullbackForm i (K β) = 0
  deg0_injectivity : ∀ (β : DiffForm E_U 0),
    extDeriv β = 0 → pullbackForm i β = 0 → β = 0
  smooth_forms_U : ∀ {n : ℕ} (ω : DiffForm E_U n), ContDiff ℝ ⊤ ω

end CohomologyIsomorphism
end DeRhamConcrete
