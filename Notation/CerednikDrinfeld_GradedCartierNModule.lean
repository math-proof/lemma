set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_CerednikDrinfeld_GradedCartierNModule.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace CerednikDrinfeld_GradedCartierNModule

scoped notation "𝕎" => WittVector p B

scoped notation "σ" => (WittVector.frobenius : WittVector p B →+* WittVector p B)

end CerednikDrinfeld_GradedCartierNModule
