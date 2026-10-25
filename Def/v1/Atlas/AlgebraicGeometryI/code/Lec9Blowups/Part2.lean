/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec9Blowups
open Polynomial


namespace Lec9Blowups

/-- The induced ring map between blowup algebras coming from
`φ : R → A`. -/
noncomputable def blowupMapRestrict {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (𝔪 : Ideal A) :
    blowupAlgebra R (𝔪.comap φ) →+* blowupAlgebra A 𝔪 :=
  (Polynomial.mapRingHom φ).restrict (blowupAlgebra R (𝔪.comap φ)) (blowupAlgebra A 𝔪)
    (fun f hf => map_mem_blowupAlgebra φ 𝔪 f hf)

end Lec9Blowups
