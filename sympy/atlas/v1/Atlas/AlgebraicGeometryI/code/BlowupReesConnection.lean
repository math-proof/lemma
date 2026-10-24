/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.BlowupChart
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BlowupChart

open Polynomial

noncomputable section

namespace BlowupReesConnection

variable (k : Type*) [CommRing k]

/-- The ideal `(X, Y) ⊂ k[X][Y]` cutting out the origin in the affine plane. -/
def originIdeal : Ideal (Polynomial (Polynomial k)) :=
  Ideal.span {C X, X}

/-- Embedding `k[X] → k[X][Y][t]` sending a polynomial to its image as a doubly-constant
coefficient; used as the scalar part of the Rees lift. -/
def coeffEmbed : Polynomial k →+* Polynomial (Polynomial (Polynomial k)) :=
  (C : Polynomial (Polynomial k) →+* Polynomial (Polynomial (Polynomial k))).comp
  (C : Polynomial k →+* Polynomial (Polynomial k))

/-- Lift of a polynomial in `k[X][Y]` to the Rees algebra by sending `Y ↦ C(Y) · t`, exhibiting
the Rees algebra structure relevant to the blow-up at the origin. -/
def reesLift : Polynomial (Polynomial k) →+* Polynomial (Polynomial (Polynomial k)) :=
  eval₂RingHom (coeffEmbed k)
    ((C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) *
     (X : Polynomial (Polynomial (Polynomial k))))

/-- Evaluation map specialising the Rees variable `t` to `X`; recovers the blow-up chart map
after composing with the Rees lift. -/
def evalAtX :
    Polynomial (Polynomial (Polynomial k)) →+* Polynomial (Polynomial k) :=
  evalRingHom (C (X : Polynomial k) : Polynomial (Polynomial k))
