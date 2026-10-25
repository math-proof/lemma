set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_WeierstrassCurve_ProjModel_ThirdLawCharts.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace WeierstrassCurve_ProjModel_ThirdLawCharts

scoped notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

scoped notation "WP₁" => kw_lrAdd_WP₁ W

scoped notation "WP₂" => kw_lrAdd_WP₂ W

scoped notation "R₀" => MvPolynomial (Fin 5) ℤ

scoped notation "W₀" => kw_lrSymOC_W₀

scoped notation "P₆₀" => MvPolynomial (Fin 3 ⊕ Fin 3) R₀

scoped notation "WP₁₀" => kw_lrAdd_WP₁ W₀

scoped notation "WP₂₀" => kw_lrAdd_WP₂ W₀

scoped notation "ℬ" => ProjModelRingCR W.toProjective

scoped notation "ℬ²" => KwLRBiRing W

scoped notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

scoped notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal

scoped notation "𝒜" k => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X k : MvPolynomial (Fin 3) R))

scoped notation "𝒜²ₜ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrThird_vec W k))

end WeierstrassCurve_ProjModel_ThirdLawCharts
