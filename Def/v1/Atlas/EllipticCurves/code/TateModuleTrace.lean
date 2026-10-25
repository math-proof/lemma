/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TateModuleTrace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
universe u

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}


/-- The restriction of an endomorphism `α : E → E` to the `n`-torsion subgroup,
viewed as an additive group homomorphism `E[n] →+ E[n]`. -/
noncomputable def Isogeny.restrictTorsion
    (α : Isogeny E E) (n : ℤ) :
    (torsionSubgroup E n) →+ (torsionSubgroup E n) where
  toFun P := ⟨α.toAddMonoidHom P.val,
    map_mem_torsionSubgroup α.toAddMonoidHom n P.val P.property⟩
  map_zero' := by
    ext
    exact α.toAddMonoidHom.map_zero
  map_add' x y := by
    ext
    exact α.toAddMonoidHom.map_add x.val y.val

/-- Given an additive endomorphism `f` of `(ZMod n)²`, extract its matrix
`Mat₂(ZMod n)` with respect to the standard basis `(1,0), (0,1)`. -/
noncomputable def torsionMatrixFromEndomorphism (n : ℕ)
    (f : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) :
    Matrix (Fin 2) (Fin 2) (ZMod n) :=
  Matrix.of fun i j =>
    let basisVec : ZMod n × ZMod n := if j = (0 : Fin 2) then (1, 0) else (0, 1)
    let img := f basisVec
    if i = (0 : Fin 2) then img.1 else img.2

/-- The matrix of `α` acting on the `n`-torsion `E[n]`, computed by conjugating
the restriction with an isomorphism `e : E[n] ≃+ (ZMod n)²` to standard basis. -/
noncomputable def Isogeny.torsionMatrix
    (α : Isogeny E E) (n : ℕ)
    (e : (torsionSubgroup E (n : ℤ)) ≃+ (ZMod n × ZMod n)) :
    Matrix (Fin 2) (Fin 2) (ZMod n) :=
  torsionMatrixFromEndomorphism n
    (e.toAddMonoidHom.comp ((α.restrictTorsion (n : ℤ)).comp e.symm.toAddMonoidHom))

/-- The trace mod `n` of `α` on the `n`-torsion: the trace of `α.torsionMatrix n e`. -/
noncomputable def Isogeny.torsionTrace
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E) (n : ℕ)
    (e : (torsionSubgroup E (n : ℤ)) ≃+ (ZMod n × ZMod n)) : ZMod n :=
  Matrix.trace (α.torsionMatrix n e)

/-- The determinant mod `n` of `α` on the `n`-torsion: the determinant of
`α.torsionMatrix n e`. -/
noncomputable def Isogeny.torsionDet
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E) (n : ℕ)
    (e : (torsionSubgroup E (n : ℤ)) ≃+ (ZMod n × ZMod n)) : ZMod n :=
  Matrix.det (α.torsionMatrix n e)

