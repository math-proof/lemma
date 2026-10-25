set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_DedekindDomain_Completion_BaseChange.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace DedekindDomain_Completion_BaseChange

scoped notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))

end DedekindDomain_Completion_BaseChange
