/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusOnePlaneCubic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ArithmeticGeometry.code.GenusOnePlaneCubic
/-- A smooth projective curve over a field $k$ packaged as: an underlying scheme (with proofs of
integrality, Krull dimension one, nonemptiness), a structure morphism to $\mathrm{Spec}\,k$, and a
(declared) genus value. The smoothness is left implicit. -/
/-- The genus of a smooth projective curve, given by the structural field `genusVal`. -/


namespace SmoothProjectiveCurveOverField

end SmoothProjectiveCurveOverField

noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory

/-- The genus of $C$ equals the genus of $F$ whenever $C$ is $k$-isomorphic to the plane cubic
$F$. -/
def WeierstrassCurve.toPlaneCubic {k : Type*} [Field k] (W : WeierstrassCurve k) :
    PlaneCubic k where
  poly :=
    let X := MvPolynomial.X (R := k) (0 : Fin 3)
    let Y := MvPolynomial.X (R := k) (1 : Fin 3)
    let Z := MvPolynomial.X (R := k) (2 : Fin 3)
    Y ^ 2 * Z + C W.a₁ * X * Y * Z + C W.a₃ * Y * Z ^ 2
      - X ^ 3 - C W.a₂ * X ^ 2 * Z - C W.a₄ * X * Z ^ 2 - C W.a₆ * Z ^ 3
  isHomogeneous := by
    have hX : (MvPolynomial.X (R := k) (0 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 0
    have hY : (MvPolynomial.X (R := k) (1 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 1
    have hZ : (MvPolynomial.X (R := k) (2 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 2
    have h1 : ((MvPolynomial.X (1 : Fin 3)) ^ 2 * (MvPolynomial.X (2 : Fin 3)) :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := (hY.pow 2).mul hZ; simpa using this
    have h2 : (C W.a₁ * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3) *
        MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₁).mul hX).mul hY |>.mul hZ; simpa using this
    have h3 : (C W.a₃ * MvPolynomial.X (1 : Fin 3) * (MvPolynomial.X (2 : Fin 3)) ^ 2 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₃).mul hY).mul (hZ.pow 2); simpa using this
    have h4 : ((MvPolynomial.X (0 : Fin 3)) ^ 3 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := hX.pow 3; simpa using this
    have h5 : (C W.a₂ * (MvPolynomial.X (0 : Fin 3)) ^ 2 * MvPolynomial.X (2 : Fin 3) :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₂).mul (hX.pow 2)).mul hZ; simpa using this
    have h6 : (C W.a₄ * MvPolynomial.X (0 : Fin 3) * (MvPolynomial.X (2 : Fin 3)) ^ 2 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₄).mul hX).mul (hZ.pow 2); simpa using this
    have h7 : (C W.a₆ * (MvPolynomial.X (2 : Fin 3)) ^ 3 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := (isHomogeneous_C (Fin 3) W.a₆).mul (hZ.pow 3); simpa using this
    exact ((h1.add h2).add h3).sub h4 |>.sub h5 |>.sub h6 |>.sub h7
  ne_zero := by
    intro h
    have := congr_arg (MvPolynomial.eval (fun i : Fin 3 => if i = 0 then (1 : k) else 0)) h
    simp only [map_sub, map_add, map_mul, map_pow, eval_X, eval_C, map_zero] at this
    simp only [show (2 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 0 from by decide,
      if_false, if_true] at this
    norm_num at this

end
