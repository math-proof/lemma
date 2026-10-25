/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec7Products.Part2
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


namespace Lec7Products

section Goal62

/-- The Segre algebra homomorphism sending `X_{(i,j)} ↦ X_i ⊗ X_j`,
underlying the Segre embedding for Lec 7, Prop 8. -/
noncomputable def segreAlgHom (R : Type*) [CommRing R] (n m : ℕ) :
    MvPolynomial (Fin n × Fin m) R →ₐ[R]
    MvPolynomial (Fin n) R ⊗[R] MvPolynomial (Fin m) R :=
  MvPolynomial.aeval (fun p =>
    MvPolynomial.X p.1 ⊗ₜ[R] MvPolynomial.X p.2)

/-- The graph morphism `Γ_f : X ⟶ X × Y` of `f : X ⟶ Y`
(Lec 7, Def 18). -/
noncomputable def graphMorphism {X Y : Scheme} (f : X ⟶ Y) : X ⟶ X ⨯ Y :=
  Limits.prod.lift (𝟙 X) f

end Goal62
end Lec7Products
