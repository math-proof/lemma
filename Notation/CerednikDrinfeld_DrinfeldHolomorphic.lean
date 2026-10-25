set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_CerednikDrinfeld_DrinfeldHolomorphic.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace CerednikDrinfeld_DrinfeldHolomorphic

scoped notation "𝔭" => Valued.v (algebraMap K₀ K ϖ.ϖ)

end CerednikDrinfeld_DrinfeldHolomorphic
