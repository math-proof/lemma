set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_RatIdele_Normalizer.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace RatIdele_Normalizer

scoped notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ

scoped notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

end RatIdele_Normalizer
