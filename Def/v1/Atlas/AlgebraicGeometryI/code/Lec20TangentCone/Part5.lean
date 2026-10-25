/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.Scheme
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The induced ring endomorphism of the associated graded ring `gr_I(R)` coming from
the `R*`-scaling action on the Rees algebra. -/
noncomputable def scaleOnGraded (I : Ideal R) (c : R) :
    assocGradedRing I →+* assocGradedRing I :=
  Ideal.Quotient.lift (reesIdealFromBase I)
    ((Ideal.Quotient.mk (reesIdealFromBase I)).comp (scaleOnRees I c))
    (fun x hx => by
      show Ideal.Quotient.mk _ (scaleOnRees I c x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact reesIdealFromBase_le_comap_scaleOnRees I c hx)

/-- The canonical ring homomorphism `R → gr_𝔪(R)`, factoring through the structure map
into the Rees algebra and the quotient projection. -/
noncomputable def ringHomToAssocGraded (𝔪 : Ideal R) : R →+* assocGradedRing 𝔪 :=
  (Ideal.Quotient.mk (reesIdealFromBase 𝔪)).comp (algebraMap R (reesAlgebra 𝔪))

/-- The tangent cone `C_x X := Spec(gr_𝔪 O_{X,x})` of `X = Spec R` at the point cut out by `𝔪`. -/
noncomputable def tangentCone (𝔪 : Ideal R) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (assocGradedRing 𝔪))

end Lec20TangentCone
