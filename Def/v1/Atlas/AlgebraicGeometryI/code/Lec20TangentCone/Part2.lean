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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The ring endomorphism of the Rees algebra `reesAlgebra I` induced by scaling `X ↦ c · X`. -/
noncomputable def scaleOnRees (I : Ideal R) (c : R) : reesAlgebra I →+* reesAlgebra I where
  toFun f := ⟨scaleAlgHom c f.val, scaleAlgHom_mem_reesAlgebra I c f.val f.prop⟩
  map_one' := Subtype.ext (map_one (scaleAlgHom c))
  map_mul' x y := Subtype.ext (map_mul (scaleAlgHom c) x.val y.val)
  map_zero' := Subtype.ext (map_zero (scaleAlgHom c))
  map_add' x y := Subtype.ext (map_add (scaleAlgHom c) x.val y.val)

end Lec20TangentCone
