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
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties
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

/-- Algebra structure on the associated graded ring over the Rees algebra. -/
noncomputable instance assocGradedRing.algebraRees (𝔪 : Ideal R) :
    Algebra (↥(reesAlgebra 𝔪)) (assocGradedRing 𝔪) := by
  unfold assocGradedRing; exact Ideal.Quotient.algebra _

end Prop34Blowup
end
