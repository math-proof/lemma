set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_WeierstrassCurve_ProjModel_GroupLawVocabulary.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace WeierstrassCurve_ProjModel_GroupLawVocabulary

scoped notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

scoped notation "WP₁" => kw_lrAdd_WP₁ W

scoped notation "WP₂" => kw_lrAdd_WP₂ W

scoped notation "R₀" => MvPolynomial (Fin 5) ℤ

scoped notation "ℬ" => ProjModelRingCR W.toProjective

scoped notation "ℬ²" => KwLRBiRing W

scoped notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

scoped notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal

scoped notation "𝒜²" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_vec W k))

scoped notation "𝒜²ₛ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_vec W k))

scoped notation "E" => projModelCR W.toProjective

scoped notation "π" => projModelStrCR W.toProjective

scoped notation "negSubst" => kw_lrAddNegDiag_negSubst W

scoped notation "negGradedHom" => kw_lrAddNegDiag_negGradedHom W

scoped notation "negMor" => kw_lrAddNegDiag_negMor W

scoped notation "evalNeg" => kw_lrAddNegDiag_evalNeg W

scoped notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover

scoped notation "gen" => kw_lrChart_gen W

scoped notation "dehom" => kw_lrChart_dehom W

scoped notation "t_F" => kw_lrAptb_tF (R := R) F

scoped notation "awayι₃" i => Proj.awayι (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R)) (kw_pbac_mk_X_mem_one_CR R W.toProjective i) one_pos

scoped notation "W_F" => kw_lrApt_WF W F

end WeierstrassCurve_ProjModel_GroupLawVocabulary

namespace WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

scoped notation "𝒜" k => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X k : MvPolynomial (Fin 3) R))

end WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

namespace WeierstrassCurve_ProjModel_GroupLawVocabulary.v1

scoped notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))

end WeierstrassCurve_ProjModel_GroupLawVocabulary.v1

namespace WeierstrassCurve_ProjModel_GroupLawVocabulary.v2

scoped notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))

end WeierstrassCurve_ProjModel_GroupLawVocabulary.v2
