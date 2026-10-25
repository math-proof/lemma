/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint.Part2
open Polynomial AlgebraicGeometry


noncomputable section

namespace BlowupAtPoint

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The blow-up scheme of `Spec R` along the ideal `I`, defined as `Proj` of the Rees algebra. -/
def blowupScheme : Scheme :=
  Proj (reesGrading I)

/-- The natural projection from the blow-up to `Spec` of the degree-zero piece (canonically
identified with `Spec R`). -/
def blowupProjection :
    blowupScheme I ⟶ Spec (.of ↥(reesGrading I 0)) :=
  Proj.toSpecZero (reesGrading I)

/-- Proper transform of a closed subscheme `Z` along a morphism `π : X ⟶ Y`, removing the
center `C`: take the closure of the preimage of `Z \ C` in `X`. -/
def properTransform {X Y : Scheme} (π : X ⟶ Y)
    (Z C : TopologicalSpace.Closeds Y.toTopCat) :
    TopologicalSpace.Closeds X.toTopCat :=
  TopologicalSpace.Closeds.closure (π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat)))

/-- Exceptional locus of a morphism `π : X ⟶ Y` over a closed subscheme `C ⊂ Y`: the preimage
of `C` in `X`. -/
def exceptionalLocus {X Y : Scheme} (π : X ⟶ Y)
    (C : TopologicalSpace.Closeds Y.toTopCat) :
    TopologicalSpace.Closeds X.toTopCat :=
  ⟨π.base ⁻¹' (C : Set Y.toTopCat), C.isClosed'.preimage π.base.hom'.continuous⟩

/-- The blow-up of the closed subscheme `Z ⊂ Spec R` at the center `C`: the proper transform
along the blow-up projection. -/
def blowupAtPoint
    (Z C : TopologicalSpace.Closeds (Spec (.of ↥(reesGrading I 0))).toTopCat) :
    TopologicalSpace.Closeds (blowupScheme I).toTopCat :=
  properTransform (blowupProjection I) Z C

/-- The exceptional locus of the blow-up of `Z` at the center `C`: the intersection of the
proper transform with the preimage of `C`. -/
def blowupExceptionalLocus
    (Z C : TopologicalSpace.Closeds (Spec (.of ↥(reesGrading I 0))).toTopCat) :
    TopologicalSpace.Closeds (blowupScheme I).toTopCat :=
  ⟨(blowupAtPoint I Z C : Set _) ∩ (exceptionalLocus (blowupProjection I) C : Set _),
   IsClosed.inter (blowupAtPoint I Z C).isClosed'
     (exceptionalLocus (blowupProjection I) C).isClosed'⟩

end BlowupAtPoint
end
