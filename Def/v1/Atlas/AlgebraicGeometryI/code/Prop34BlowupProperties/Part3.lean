/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BlowupAtPoint
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- The induced scaling ring homomorphism on the Rees algebra. -/
noncomputable def scaleOnRees (I : Ideal R) (c : R) : reesAlgebra I →+* reesAlgebra I where
  toFun f := ⟨scaleAlgHom c f.val, scaleAlgHom_mem_reesAlgebra I c f.val f.prop⟩
  map_one' := Subtype.ext (map_one (scaleAlgHom c))
  map_mul' x y := Subtype.ext (map_mul (scaleAlgHom c) x.val y.val)
  map_zero' := Subtype.ext (map_zero (scaleAlgHom c))
  map_add' x y := Subtype.ext (map_add (scaleAlgHom c) x.val y.val)

end Prop34Blowup
end
