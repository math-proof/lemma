import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.DivisorLineRatio
open CurveDivisor EllipticCurveP2Data


namespace EllipticCurveP2Data

/--
[pdiv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DivisorLineRatio.lean)
-/
@[path]
lemma pdiv_mul
  [Field F]
  {E : EllipticCurveP2Data C F}
  {f g : Fˣ} :
-- imply
  E.pdiv (f * g) = E.pdiv f + E.pdiv g := by
-- proof
  simp only [pdiv]
  exact @CurveWithOrd.principalDivisor_mul C F _ E.curveInst f g

end EllipticCurveP2Data

namespace EllipticCurveP2Data

/--
[pdiv_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DivisorLineRatio.lean)
-/
@[path]
lemma pdiv_inv
  [Field F]
  {E : EllipticCurveP2Data C F}
  {f : Fˣ} :
-- imply
  E.pdiv f⁻¹ = -E.pdiv f := by
-- proof
  simp only [pdiv]
  exact @CurveWithOrd.principalDivisor_inv C F _ E.curveInst f
end EllipticCurveP2Data



-- created on 2026-10-23
