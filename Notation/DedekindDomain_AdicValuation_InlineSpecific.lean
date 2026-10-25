set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace DedekindDomain_AdicValuation_InlineSpecific

scoped notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

end DedekindDomain_AdicValuation_InlineSpecific
