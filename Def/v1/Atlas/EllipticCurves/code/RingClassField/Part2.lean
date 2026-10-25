/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import Lemma.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7
import Structure.v1.Atlas.EllipticCurves.code.RingClassField


namespace Elliptic_Curves

/-- The Hilbert class polynomial of discriminant `D` viewed as a polynomial
over an arbitrary field `F`, obtained by base change from the integral form. -/
noncomputable def hilbertClassPolynomial (D : ℤ) (F : Type*) [Field F] : Polynomial F :=
  (Elliptic_Curves.hilbertClassPolynomialZ D).map (Int.castRingHom F)

/-- `Ell_𝒪(F)`: the set of `j`-invariants of elliptic curves over the finite
field `F` whose endomorphism ring is the order of discriminant `D`. -/

end Deuring

open NumberField

noncomputable section

namespace DeuringLifting

/-- `IsReductionOfCurve E E_star 𝔮 e` is the predicate stating that the curve
`E_star` over the number field `L` has good reduction modulo the prime `𝔮`
identifying with `E` via the ring isomorphism `e : F ≃+* 𝒪_L/𝔮`. -/
opaque IsReductionOfCurve
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {L : Type} [Field L] [DecidableEq L] [NumberField L]
    (E : WeierstrassCurve.Affine F)
    (E_star : WeierstrassCurve.Affine L)
    (𝔮 : Ideal (𝓞 L)) [𝔮.IsMaximal]
    (e : F ≃+* (𝓞 L ⧸ 𝔮)) : Prop

/-- `IsReductionOfEndomorphism` states that the endomorphism `φ_star` of the
lift `E_star` reduces to the endomorphism `φ` of `E` modulo `𝔮`, given that
`E_star` is a good reduction lift of `E`. -/
opaque IsReductionOfEndomorphism
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {L : Type} [Field L] [DecidableEq L] [NumberField L]
    (E : WeierstrassCurve.Affine F)
    (E_star : WeierstrassCurve.Affine L)
    (φ : AddMonoid.End E.Point)
    (φ_star : AddMonoid.End E_star.Point)
    (𝔮 : Ideal (𝓞 L)) [𝔮.IsMaximal]
    (e : F ≃+* (𝓞 L ⧸ 𝔮))
    (hcurve : IsReductionOfCurve E E_star 𝔮 e) : Prop

end DeuringLifting
end
