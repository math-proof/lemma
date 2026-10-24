import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.FermatsLastTheorem
open Matrix CongruenceSubgroup FLT EllipticCurve


/--
[conductor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean)
-/
@[path]
private lemma conductor_pos_eq
  {E : EllipticCurveOverQ} :
-- imply
  0 < conductor E := by
-- proof
  apply FLT.conductor_pos E

/--
[ribetLevelDivisor_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean)
-/
@[path]
private lemma ribetLevelDivisor_dvd_eq
  {E : EllipticCurveOverQ}
  {ℓ : ℕ} :
-- imply
  ribetLevelDivisor E ℓ ∣ conductor E := by
-- proof
  apply FLT.ribetLevelDivisor_dvd E ℓ

/--
[ribetLevelDivisor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean)
-/
@[path]
private lemma ribetLevelDivisor_pos_eq
  {E : EllipticCurveOverQ}
  {ℓ : ℕ} :
-- imply
  0 < ribetLevelDivisor E ℓ := by
-- proof
  apply FLT.ribetLevelDivisor_pos E ℓ

/--
[conductor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean)
-/
@[path]
private lemma conductor_pos_eq_2
  {E : FLT.EllipticCurveOverQ} :
-- imply
  0 < conductor E := by
-- proof
  apply EllipticCurve.conductor_pos E


-- created on 2026-10-23
