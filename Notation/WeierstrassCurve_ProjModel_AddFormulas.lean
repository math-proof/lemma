set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_WeierstrassCurve_ProjModel_AddFormulas.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace WeierstrassCurve_ProjModel_AddFormulas

scoped notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

scoped notation "P₈" => MvPolynomial ((Fin 3 ⊕ Fin 3) ⊕ Fin 2) R

scoped notation "Xl" i => (X (Sum.inl i) : P₆)

scoped notation "Xr" i => (X (Sum.inr i) : P₆)

scoped notation "WP₁" => kw_lrAdd_WP₁ W

scoped notation "WP₂" => kw_lrAdd_WP₂ W

scoped notation "ι" => (rename (Sum.inl : (Fin 3 ⊕ Fin 3) → (Fin 3 ⊕ Fin 3) ⊕ Fin 2) : P₆ →ₐ[R] P₈)

scoped notation "𝓈" => (X (Sum.inr 0) : P₈)

scoped notation "𝓉" => (X (Sum.inr 1) : P₈)

scoped notation "c₂₁" => kw_lrAdd_c₂₁ W

scoped notation "c₁₂" => kw_lrAdd_c₁₂ W

scoped notation "σ" => kw_lrAdd_spec W

scoped notation "τ" => (rename (Sum.swap : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3) : P₆ →ₐ[R] P₆)

scoped notation "δ" => (aeval (Sum.elim X X) : P₆ →ₐ[R] MvPolynomial (Fin 3) R)

end WeierstrassCurve_ProjModel_AddFormulas
