import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.IdealNorm
open IdealNorm


namespace IdealNorm

/--
[idealNorm_eq_card_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealNorm.lean)
-/
@[path]
lemma idealNorm_eq_card_quotient
  [CommRing 𝒪]
  {𝔞 : Ideal 𝒪} :
-- imply
  idealNorm 𝔞 = Nat.card (𝒪 ⧸ 𝔞) :=
-- proof
  Submodule.cardQuot_apply 𝔞

end IdealNorm

namespace IdealNorm

/--
[idealNorm_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealNorm.lean)
-/
@[path]
lemma idealNorm_top
  [CommRing 𝒪] :
-- imply
  idealNorm (⊤ : Ideal 𝒪) = 1 :=
-- proof
  Submodule.cardQuot_top 𝒪 𝒪

end IdealNorm

namespace IdealNorm

/--
[idealNorm_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealNorm.lean)
-/
@[path]
lemma idealNorm_bot
  [CommRing 𝒪]
  [Infinite 𝒪] :
-- imply
  idealNorm (⊥ : Ideal 𝒪) = 0 :=
-- proof
  Submodule.cardQuot_bot 𝒪 𝒪

end IdealNorm

namespace IdealNorm

/--
[idealNorm_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealNorm.lean)
-/
@[path]
lemma idealNorm_pos
  [CommRing 𝒪]
  [CommRing 𝒪]
  [IsDomain 𝒪]
  [Module.Free ℤ 𝒪]
  [Module.Finite ℤ 𝒪]
  {𝔞 : Ideal 𝒪}
-- given
  (h : 𝔞 ≠ ⊥) :
-- imply
  0 < idealNorm 𝔞 := by
-- proof
  rw [idealNorm, Submodule.cardQuot_apply, Nat.pos_iff_ne_zero, Nat.card_ne_zero]
  exact ⟨⟨Ideal.Quotient.mk 𝔞 0⟩, Ideal.finiteQuotientOfFreeOfNeBot 𝔞 h⟩

end IdealNorm

namespace IdealNorm

/--
[idealNorm_eq_absNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealNorm.lean)
-/
@[path]
lemma idealNorm_eq_absNorm
  [CommRing 𝒪]
  [CommRing 𝒪]
  [Nontrivial 𝒪]
  [IsDedekindDomain 𝒪]
  [Module.Free ℤ 𝒪]
  {𝔞 : Ideal 𝒪} :
-- imply
  Ideal.absNorm 𝔞 = idealNorm 𝔞 :=
-- proof
  Ideal.absNorm_apply 𝔞

end IdealNorm


-- created on 2026-10-23
