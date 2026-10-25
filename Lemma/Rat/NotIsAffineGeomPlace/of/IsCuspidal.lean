import Mathlib
import sympy.Basic
import Def.ModularCurve_ProlongationTuple
import Lemma.Int.P2MUtil

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

/--
[ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal.lean)
-/
@[path]
private lemma main
  [Field k]
  {q : ℕ} [Fact q.Prime] [CharP k q]
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N]
  {red : A →+* k}
  {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
-- given
  (hV : ProlongationTuple.IsCuspidal P V) :
-- imply
  ¬ IsAffineGeomPlace k N (P.reduceFst V) := by
-- proof
  set jN : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ with hjN
  have hαj : heckeAlphaBar (AlgebraicClosure ℚ) N q jN = ProlongationTuple.jFun N q :=
    Subtype.ext (coe_heckeAlphaBar N q jN)
  have he : 0 < Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) V := by
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    exact V.ramificationIndex_pos (F := modularFunctionFieldBar N)

  have hcusp : ∀ a : A, (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have hle := hV a
    have key := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [map_sub, hαj, AlgHom.commutes] at key
    rw [key] at hle
    by_contra hpos
    push_neg at hpos
    exact absurd hle (not_le.mpr (mul_pos (by exact_mod_cast he) hpos))
  have hpole := P.d0_j_pole (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hcusp
  intro haff
  have h0 := (P.reduceFst V).ord_nonneg_of_mem haff.1
  exact absurd hpole (not_lt.mpr h0)


-- created on 2026-10-23
