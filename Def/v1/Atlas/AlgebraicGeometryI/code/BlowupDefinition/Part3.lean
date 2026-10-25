/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.BlowupDefinition.Part2
open Polynomial AlgebraicGeometry


noncomputable section

namespace Blowup

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The blow-up of `Spec R` along the ideal `I` (Def 20, Lec 9): `Proj` of the Rees algebra. -/
def blowupAlong : Scheme :=
  AlgebraicGeometry.Proj (reesGrading I)

/-- Natural projection from the blow-up `Bl_I(Spec R)` down to `Spec` of the degree-zero piece,
canonically identified with `Spec R`. -/
def blowupProjection :
    blowupAlong I ⟶ AlgebraicGeometry.Spec (.of ↥(reesGrading I 0)) :=
  AlgebraicGeometry.Proj.toSpecZero (reesGrading I)

/-- Proper transform of a closed subset `Z` along `π : X ⟶ Y`, away from the center `C`:
the closure in `X` of the preimage of `Z \ C`. -/
def properTransformSet {X Y : Scheme} (π : X ⟶ Y)
    (Z C : TopologicalSpace.Closeds Y.toTopCat) :
    TopologicalSpace.Closeds X.toTopCat :=
  TopologicalSpace.Closeds.closure (π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat)))

/-- Exceptional locus of `π : X ⟶ Y` over a closed subscheme `C ⊂ Y`, defined as `π⁻¹(C)`. -/
def exceptionalLocusSet {X Y : Scheme} (π : X ⟶ Y)
    (C : TopologicalSpace.Closeds Y.toTopCat) :
    TopologicalSpace.Closeds X.toTopCat :=
  ⟨π.base ⁻¹' (C : Set Y.toTopCat), C.isClosed'.preimage π.base.hom'.continuous⟩

/-- The proper transform of a closed subscheme `Z` along the blow-up projection, viewed as a
closed subset of the blow-up. -/
def blowupAtCenter
    (Z C : TopologicalSpace.Closeds (Spec (.of ↥(reesGrading I 0))).toTopCat) :
    TopologicalSpace.Closeds (blowupAlong I).toTopCat :=
  properTransformSet (blowupProjection I) Z C

/-- The exceptional locus of the blow-up of `Z`: the intersection of the proper transform with
the preimage of the center `C`. -/
def blowupExceptionalLocus
    (Z C : TopologicalSpace.Closeds (Spec (.of ↥(reesGrading I 0))).toTopCat) :
    TopologicalSpace.Closeds (blowupAlong I).toTopCat :=
  ⟨(blowupAtCenter I Z C : Set _) ∩ (exceptionalLocusSet (blowupProjection I) C : Set _),
   IsClosed.inter (blowupAtCenter I Z C).isClosed'
     (exceptionalLocusSet (blowupProjection I) C).isClosed'⟩

end Blowup
end
