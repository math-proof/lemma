module
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
public import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

variable (k : Type*) [Field k]

open MvPolynomial

/-- The pullback ring homomorphism $\varphi^* : \bar{k}[Y] \to \bar{k}[X]$ induced by an affine morphism $\varphi : X \to Y$. -/
def AffineMorphism.pullback {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y) :
    AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X :=
  Ideal.Quotient.lift (idealOfAlgebraicSet Y)
    ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp
      (MvPolynomial.bind₁ φ.polys).toRingHom)
    (fun f hf => by
      simp only [AlgHom.toRingHom_eq_coe]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (bind₁_mem_idealOfAlgebraicSet_of_maps_to k φ.polys φ.maps_to hf))

end
