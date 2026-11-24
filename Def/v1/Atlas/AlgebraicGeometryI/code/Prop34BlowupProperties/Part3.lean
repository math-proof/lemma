module
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint.Part3
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BlowupAtPoint
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties
open Polynomial AlgebraicGeometry


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
