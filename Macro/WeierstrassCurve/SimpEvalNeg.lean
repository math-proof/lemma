/-!
# `simp_evalNeg` tactic macro

Carved from `Lemma.Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary`.
Identifiers resolve at the use site (`kw_lrAddNegDiag_*`, `Matrix.*`, `map_*`).
-/

/-- Simplify with the `kw_lrAddNegDiag_evalNeg` lemma pack. -/
macro "simp_evalNeg" : tactic =>
  `(tactic| simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one,
    kw_lrAddNegDiag_evalNeg_C, kw_lrAddNegDiag_evalNeg_inr,
    kw_lrAddNegDiag_evalNeg_inl, kw_lrAddNegDiag_negSubstGen,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons])
