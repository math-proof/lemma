import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzSheafIso
open Ideal UniqueFactorizationMonoid RiemannHurwitzSheaf


namespace RiemannHurwitzSheaf

/--
[differentIdeal_dvd_pow_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheafIso.lean)
-/
@[path]
lemma differentIdeal_dvd_pow_sub_one
  {A : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {p : Ideal A}
  [p.IsMaximal]
  {P : Ideal B}
  [P.IsMaximal]
  [P.LiesOver p]
-- given
  (hp : p ≠ ⊥) :
-- imply
  P ^ (p.ramificationIdx P - 1) ∣ differentIdeal A B :=
-- proof
  pow_sub_one_dvd_differentIdeal A P (p.ramificationIdx P) hp
    (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
/-- In the tame case, `P^{e_P}` does not divide the different ideal `𝔡_{B/A}`,
so the exponent of `P` in `𝔡_{B/A}` is exactly `e_P - 1`. -/

end RiemannHurwitzSheaf


-- created on 2026-10-23
