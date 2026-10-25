set_option quotPrecheck false
set_option hygiene false

/-!
# Semialgebra homomorphism notation

Carved from `Lemma/Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean`.
`A →ₛₐ[φ] B` denotes `SemialgHom φ A B`. That structure stays in the
Definitions module, which imports this one, so the right-hand side is
resolved when the notation is used.
-/

infixr:25 " →ₛₐ " => SemialgHom _

notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B
