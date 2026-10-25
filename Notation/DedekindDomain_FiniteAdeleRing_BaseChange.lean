set_option quotPrecheck false
set_option hygiene false

/-!
# Continuous semialgebra homomorphism notation

Carved from `Lemma/Definitions/Def_DedekindDomain_FiniteAdeleRing_BaseChange.lean`.
`A →SA[φ] B` denotes `ContinuousSemialgHom φ A B`. That structure stays in
the Definitions module, which imports this one, so the right-hand side is
resolved when the notation is used.
-/

infixr:25 " →SA " => ContinuousSemialgHom _

notation:25 A " →SA[" φ:25 "] " B:0 => ContinuousSemialgHom φ A B
