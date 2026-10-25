/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingProjDef38.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Scheme
import Instance.v1.Atlas.AlgebraicGeometryI.code.GradedRingProjDef38
set_option maxHeartbeats 400000


noncomputable section

open Polynomial AlgebraicGeometry

variable {R : Type*} [CommRing R]

namespace Definition38

/-- Canonical ring map `R → gr_𝔪(R)` factoring through the Rees algebra and quotient. -/
noncomputable def ringHomToAssocGraded (𝔪 : Ideal R) : R →+* assocGradedRing 𝔪 :=
  (Ideal.Quotient.mk (reesIdealFromBase 𝔪)).comp (algebraMap R (reesAlgebra 𝔪))

/-- The tangent cone (Def 38, Lec 19): `T_x X = Spec(gr_𝔪(O_{X,x}))` for the maximal ideal `𝔪`. -/
noncomputable def tangentCone (𝔪 : Ideal R) : Scheme :=
  Spec (.of (assocGradedRing 𝔪))

/-- The canonical morphism `tangentCone 𝔪 → Spec R` induced by `R → gr_𝔪(R)`. -/
noncomputable def tangentConeMap (𝔪 : Ideal R) :
    tangentCone 𝔪 ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (ringHomToAssocGraded 𝔪))

end Definition38
end
