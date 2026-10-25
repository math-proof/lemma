set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_LocalGL2_Kirillov.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace LocalGL2_Kirillov

scoped notation "F" => HeightOneSpectrum.adicCompletion K v

scoped notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

scoped notation "Fx" => (HeightOneSpectrum.adicCompletion K v)ˣ

scoped notation "Γ" => (WithZero (Multiplicative ℤ))ˣ

end LocalGL2_Kirillov
