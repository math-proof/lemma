import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
open StatMech StatMech.Onsager


/--
[ons_finsuppTotalDegree_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsuppTotalDegree_add_eq
  [DecidableEq E]
  {m n : E →₀ ℕ} :
-- imply
  ons_finsuppTotalDegree (m + n) = ons_finsuppTotalDegree m + ons_finsuppTotalDegree n := by
-- proof
  apply StatMech.Onsager.ons_finsuppTotalDegree_add m n

/--
[ons_finsuppTotalDegree_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsuppTotalDegree_single_eq
  [DecidableEq E]
  {edge : E}
  {n : ℕ} :
-- imply
  ons_finsuppTotalDegree (Finsupp.single edge n) = n := by
-- proof
  apply StatMech.Onsager.ons_finsuppTotalDegree_single edge n

/--
[ons_finsuppTotalDegree_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsuppTotalDegree_finset_sum_eq
  [Fintype I]
  [DecidableEq E]
  {m : I → E →₀ ℕ} :
-- imply
  ons_finsuppTotalDegree (∑ i, m i) = ∑ i, ons_finsuppTotalDegree (m i) := by
-- proof
  apply StatMech.Onsager.ons_finsuppTotalDegree_finset_sum m

/--
[ons_decTransitionExponent_totalDegree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decTransitionExponent_totalDegree_pos_eq
  {L : ℕ}
  {d₂ d₁ : ons_Dart L} :
-- imply
  0 < ons_finsuppTotalDegree (ons_decTransitionExponent L d₂ d₁) := by
-- proof
  apply StatMech.Onsager.ons_decTransitionExponent_totalDegree_pos L d₂ d₁

/--
[ons_decLoopExponent_length_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decLoopExponent_length_le_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L} :
-- imply
  n ≤ ons_finsuppTotalDegree (ons_decLoopExponent L d) := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_length_le L d

/--
[ons_decFormalLogCoeff_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_eq_tsum_eq
  {L : ℕ}
  [NeZero L]
  {omega u v : ℂ}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ons_decFormalLogCoeff L omega u v m = -(∑' r : ℕ, (∑ d : Fin (r + 1) → ons_Dart L, if ons_decLoopExponent L d = m then ons_decLoopScalar L omega u v d else 0) / ((r : ℂ) + 1)) / 2 := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_eq_tsum L omega u v m

/--
[ons_decFormalLog_constantCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decFormalLog_constantCoeff_eq
  {L : ℕ}
  [NeZero L]
  {omega u v : ℂ} :
-- imply
  MvPowerSeries.constantCoeff (ons_decFormalLog L omega u v) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalLog_constantCoeff L omega u v

/--
[ons_decFormalLog_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decFormalLog_hasSubst_eq
  {L : ℕ}
  [NeZero L]
  {omega u v : ℂ} :
-- imply
  PowerSeries.HasSubst (ons_decFormalLog L omega u v) := by
-- proof
  apply StatMech.Onsager.ons_decFormalLog_hasSubst L omega u v

/--
[ons_finsetExponent_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsetExponent_insert_eq
  [DecidableEq E]
  {S : Finset E}
  {edge : E}
-- given
  (hedge : edge ∉ S) :
-- imply
  ons_finsetExponent (insert edge S) = Finsupp.single edge 1 + ons_finsetExponent S := by
-- proof
  apply StatMech.Onsager.ons_finsetExponent_insert S edge hedge

/--
[ons_finsetExponent_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsetExponent_image_eq
  [DecidableEq E]
  [DecidableEq F]
  {S : Finset E}
  {f : E → F}
-- given
  (hf : Set.InjOn f S) :
-- imply
  ons_finsetExponent (S.image f) = ∑ edge ∈ S, Finsupp.single (f edge) 1 := by
-- proof
  apply StatMech.Onsager.ons_finsetExponent_image S f hf

/--
[ons_finsetExponent_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsetExponent_apply_eq
  [DecidableEq E]
  {S : Finset E}
  {edge : E} :
-- imply
  ons_finsetExponent S edge = if edge ∈ S then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_finsetExponent_apply S edge

/--
[ons_finsetExponent_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsetExponent_injective_eq
  [DecidableEq E] :
-- imply
  Function.Injective (ons_finsetExponent : Finset E → E →₀ ℕ) := by
-- proof
  apply StatMech.Onsager.ons_finsetExponent_injective

/--
[ons_finsetExponent_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_finsetExponent_prod_eq
  [DecidableEq E]
  [CommMonoid R]
  {S : Finset E}
  {weight : E → R} :
-- imply
  (ons_finsetExponent S).prod (fun edge n ↦ weight edge ^ n) = ∏ edge ∈ S, weight edge := by
-- proof
  apply StatMech.Onsager.ons_finsetExponent_prod S weight

/--
[ons_decoratedSpinPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decoratedSpinPolynomial_eval_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {decWeight : ons_DecEdge L → ℂ} :
-- imply
  MvPolynomial.eval decWeight (ons_decoratedSpinPolynomial L a b) = ons_decoratedFullWeightedSpinSum L decWeight a b := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinPolynomial_eval L a b decWeight

/--
[ons_decoratedSpinPolynomial_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decoratedSpinPolynomial_coeff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  MvPolynomial.coeff (ons_finsetExponent D.1) (ons_decoratedSpinPolynomial L a b) = (ons_spinCharacter a b (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinPolynomial_coeff L a b D

/--
[ons_mvSeriesEval_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_mvSeriesEval_coe_eq
  {p : MvPolynomial E ℂ}
  {weight : E → ℂ} :
-- imply
  ons_mvSeriesEval (p : MvPowerSeries E ℂ) weight = MvPolynomial.eval weight p := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_coe p weight

/--
[ons_decoratedFormalKacWardIdentity_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean)
-/
@[path]
private lemma ons_decoratedFormalKacWardIdentity_eval_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {decWeight : ons_DecEdge L → ℂ}
-- given
  (hformal : ons_decoratedFormalKacWardIdentity L) :
-- imply
  ons_mvSeriesEval (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) decWeight = ons_decoratedFullWeightedSpinSum L decWeight a b := by
-- proof
  apply StatMech.Onsager.ons_decoratedFormalKacWardIdentity_eval L hformal a b decWeight


-- created on 2026-10-23
