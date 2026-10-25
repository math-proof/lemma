set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_LanglandsTunnell_CubicInduction_AdelicEpstein.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace LanglandsTunnell_CubicInduction_AdelicEpstein

scoped notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

scoped notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

end LanglandsTunnell_CubicInduction_AdelicEpstein
