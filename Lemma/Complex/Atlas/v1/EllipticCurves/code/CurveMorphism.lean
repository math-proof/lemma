import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.CurveMorphism.Part3
open Polynomial CurveMorphism
open scoped Polynomial.Bivariate
open ProjectiveCurve


namespace CurveMorphism

/--
[Morphism.isMorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CurveMorphism.lean)
-/
@[path]
lemma Morphism.isMorphism
  {k : Type u}
  [Field k]
  {f₁ f₂ : k[X][Y]}
  [IsDomain (CoordinateRing f₁)]
  {φ : Morphism f₁ f₂} :
-- imply
  IsMorphism φ.toRationalMap :=
-- proof
  φ.regular_everywhere

end CurveMorphism


-- created on 2026-10-23
