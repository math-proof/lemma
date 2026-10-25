set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_WeierstrassCurve_ProjModel_ThirdAddFormulas.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace WeierstrassCurve_ProjModel_ThirdAddFormulas

scoped notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

scoped notation "Xl" i => (X (Sum.inl i) : P₆)

scoped notation "Xr" i => (X (Sum.inr i) : P₆)

scoped notation "WP₁" => kw_lrAdd_WP₁ W

scoped notation "WP₂" => kw_lrAdd_WP₂ W

scoped notation "δ" => (aeval (Sum.elim X X) : P₆ →ₐ[R] MvPolynomial (Fin 3) R)

end WeierstrassCurve_ProjModel_ThirdAddFormulas
