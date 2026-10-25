set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_CerednikDrinfeld_LubinTateModule.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace CerednikDrinfeld_LubinTateModule

scoped notation "𝕆" => Zp2 p

scoped notation "𝔮" => Fintype.card (GaloisField p 2)

scoped notation "σ" => (WittVector.frobenius : Zp2 p →+* Zp2 p)

end CerednikDrinfeld_LubinTateModule
