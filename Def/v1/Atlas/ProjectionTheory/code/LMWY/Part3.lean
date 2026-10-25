/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LMWY.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.LMWY
open Matrix


namespace HomogeneousDynamics

/-- The unipotent orbit closure of `x` stays at distance at least `η` from every proper
homogeneous subspace; the diophantine condition under which LMWY proves polynomial
density of the orbit. -/
def IsOrbitFarFromProperHomogeneous
    [PseudoMetricSpace (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)]
    (x : SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z) (η : ℝ) : Prop :=
  ∀ Y : ProperHomogeneousSubspace,
    ∀ y ∈ closure (Set.range (fun t : ℝ => unipotentElem t • x)),
      Metric.infDist y Y.carrier ≥ η

end HomogeneousDynamics
