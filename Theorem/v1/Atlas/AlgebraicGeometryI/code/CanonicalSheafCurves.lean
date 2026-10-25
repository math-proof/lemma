/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
set_option maxHeartbeats 800000

open RiemannRochCurves


noncomputable section

namespace CanonicalSheafCurves

/-- The rational numbers `ℚ` (as a `ℚ`-algebra) witness the genus-`0` case of `CurveWitness`. -/
theorem curveWitness_zero : CurveWitness 0 := by
  refine ⟨ℚ, inferInstance, ℚ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  simp only [Nat.cast_eq_zero]
  haveI := KaehlerDifferential.subsingleton_of_surjective ℚ ℚ (fun x => ⟨x, rfl⟩)
  exact Module.finrank_zero_of_subsingleton

end CanonicalSheafCurves
end
