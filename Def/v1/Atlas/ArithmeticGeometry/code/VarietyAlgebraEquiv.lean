/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9


noncomputable section

variable (k : Type*) [Field k]

open MvPolynomial

/-- Evaluation at a point $P \in X$ as a ring homomorphism $\bar{k}[X] \to \bar{k}$ from the coordinate ring. -/
def evalOnCoordRing {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X) :
    AffineCoordinateRingBar X →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet X) (MvPolynomial.eval P)
    (fun _ hf => hf P hP)

end
