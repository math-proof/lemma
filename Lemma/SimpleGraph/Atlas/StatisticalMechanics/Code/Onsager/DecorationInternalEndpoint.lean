import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalEndpoint
open StatMech StatMech.Onsager


/--
[ons_neg_one_add_eq_iff_eq_one_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_neg_one_add_eq_iff_eq_one_add_eq
  [CommRing R]
  {x y : R} :
-- imply
  -1 + x = y ↔ x = 1 + y := by
-- proof
  apply StatMech.Onsager.ons_neg_one_add_eq_iff_eq_one_add x y

/--
[ons_one_add_eq_iff_eq_neg_one_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_one_add_eq_iff_eq_neg_one_add_eq
  [CommRing R]
  {x y : R} :
-- imply
  1 + x = y ↔ x = -1 + y := by
-- proof
  apply StatMech.Onsager.ons_one_add_eq_iff_eq_neg_one_add x y

/--
[ons_decChainPathIndices_zero_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_decChainPathIndices_zero_mem_iff_eq
  {a b : Fin 4} :
-- imply
  (0 : Fin 3) ∈ ons_decChainPathIndices a b ↔ (a = 0) ≠ (b = 0) := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_zero_mem_iff a b

/--
[ons_decChainPathIndices_two_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_decChainPathIndices_two_mem_iff_eq
  {a b : Fin 4} :
-- imply
  (2 : Fin 3) ∈ ons_decChainPathIndices a b ↔ (a = 3) ≠ (b = 3) := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_two_mem_iff a b

/--
[ons_decChainCross_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_decChainCross_zero_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (loop k).1 = ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
  (hnonUturn : ∀ k : Fin n, (loop k).2 ≠ (loop (k + 1)).2 + 2) :
-- imply
  ((loop k).1 = site ∧ (0 : Fin 3) ∈ ons_decChainPathIndices ((loop (k + 1)).2 + 2) (loop k).2) ↔ loop k = (site, 0) ∨ loop (k + 1) = ons_dartRev L (site, 0) := by
-- proof
  apply StatMech.Onsager.ons_decChainCross_zero_iff L loop hvalid hnonUturn site k

/--
[ons_decChainCross_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_decChainCross_two_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (loop k).1 = ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
  (hnonUturn : ∀ k : Fin n, (loop k).2 ≠ (loop (k + 1)).2 + 2) :
-- imply
  ((loop k).1 = site ∧ (2 : Fin 3) ∈ ons_decChainPathIndices ((loop (k + 1)).2 + 2) (loop k).2) ↔ loop k = (site, 3) ∨ loop (k + 1) = ons_dartRev L (site, 3) := by
-- proof
  apply StatMech.Onsager.ons_decChainCross_two_iff L loop hvalid hnonUturn site k

/--
[ons_decLoop_nonUturn_of_scalar_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_decLoop_nonUturn_of_scalar_ne_zero_eq
  {L : ℕ}
  {omega u v : ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
-- given
  (hscalar : ons_decLoopScalar L omega u v loop ≠ 0) :
-- imply
  ∀ k : Fin n, (loop k).2 ≠ (loop (k + 1)).2 + 2 := by
-- proof
  apply StatMech.Onsager.ons_decLoop_nonUturn_of_scalar_ne_zero L omega u v loop hscalar

/--
[ons_sum_indicator_eq_visitCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_sum_indicator_eq_visitCount_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {loop : Fin n → E} :
-- imply
  (∑ k, if loop k = e then 1 else 0) = ons_visitCount e loop := by
-- proof
  apply StatMech.Onsager.ons_sum_indicator_eq_visitCount e loop

/--
[ons_decLoopExponent_chain_zero_eq_visits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_decLoopExponent_chain_zero_eq_visits_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (loop k).1 = ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
  (hnonUturn : ∀ k : Fin n, (loop k).2 ≠ (loop (k + 1)).2 + 2) :
-- imply
  ons_decLoopExponent L loop (ons_decChainEdge site 0) = ons_visitCount (site, 0) loop + ons_visitCount (ons_dartRev L (site, 0)) loop := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_chain_zero_eq_visits L loop hvalid hnonUturn site

/--
[ons_decLoopExponent_chain_two_eq_visits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_decLoopExponent_chain_two_eq_visits_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (loop k).1 = ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
  (hnonUturn : ∀ k : Fin n, (loop k).2 ≠ (loop (k + 1)).2 + 2) :
-- imply
  ons_decLoopExponent L loop (ons_decChainEdge site 2) = ons_visitCount (site, 3) loop + ons_visitCount (ons_dartRev L (site, 3)) loop := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_chain_two_eq_visits L loop hvalid hnonUturn site

/--
[ons_finsuppProd_scaleDecEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_finsuppProd_scaleDecEdgeWeight_eq
  {L : ℕ}
  {m : ons_DecEdge L →₀ ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {edge : ons_DecEdge L}
  {t : ℂ} :
-- imply
  m.prod (fun f n => ons_scaleDecEdgeWeight decWeight edge t f ^ n) = t ^ m edge * m.prod (fun f n => decWeight f ^ n) := by
-- proof
  apply StatMech.Onsager.ons_finsuppProd_scaleDecEdgeWeight m decWeight edge t

/--
[ons_prod_indicator_eq_pow_visitCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_prod_indicator_eq_pow_visitCount_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {t : ℂ}
  {loop : Fin n → E} :
-- imply
  (∏ k, if loop k = e then t else 1) = t ^ ons_visitCount e loop := by
-- proof
  apply StatMech.Onsager.ons_prod_indicator_eq_pow_visitCount e t loop

/--
[ons_loopWeight_scaleColumns_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_loopWeight_scaleColumns_pair_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {M : Matrix E E ℂ}
  {e r : E}
  {t : ℂ}
  {loop : Fin n → E}
-- given
  (her : e ≠ r) :
-- imply
  ons_loopWeight (ons_scaleColumns ({e, r} : Finset E) t M) loop = t ^ (ons_visitCount e loop + ons_visitCount r loop) * ons_loopWeight M loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_scaleColumns_pair M e r her t loop

/--
[ons_loopWeight_scale_chain_zero_eq_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_loopWeight_scale_chain_zero_eq_scaleColumns_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {t : ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 0) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop = ons_loopWeight (ons_scaleColumns ({(site, 0), ons_dartRev L (site, 0)} : Finset (ons_Dart L)) t (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_scale_chain_zero_eq_scaleColumns L decWeight a b site t loop

/--
[ons_loopWeight_scale_chain_two_eq_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_loopWeight_scale_chain_two_eq_scaleColumns_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {t : ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 2) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop = ons_loopWeight (ons_scaleColumns ({(site, 3), ons_dartRev L (site, 3)} : Finset (ons_Dart L)) t (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_scale_chain_two_eq_scaleColumns L decWeight a b site t loop

/--
[ons_detWalkRoot_eq_of_loopWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_detWalkRoot_eq_of_loopWeight_eq_eq
  [Fintype E]
  [DecidableEq E]
  {M N : Matrix E E ℂ}
-- given
  (hloop : ∀ (n : ℕ) (loop : Fin (n + 1) → E), ons_loopWeight M loop = ons_loopWeight N loop) :
-- imply
  ons_detWalkRoot M = ons_detWalkRoot N := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_eq_of_loopWeight_eq M N hloop

/--
[ons_detWalkRoot_scale_chain_zero_eq_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_detWalkRoot_scale_chain_zero_eq_scaleColumns_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {t : ℂ} :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 0) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_scaleColumns ({(site, 0), ons_dartRev L (site, 0)} : Finset (ons_Dart L)) t (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scale_chain_zero_eq_scaleColumns L decWeight a b site t

/--
[ons_detWalkRoot_scale_chain_two_eq_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_detWalkRoot_scale_chain_two_eq_scaleColumns_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {t : ℂ} :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 2) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_scaleColumns ({(site, 3), ons_dartRev L (site, 3)} : Finset (ons_Dart L)) t (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scale_chain_two_eq_scaleColumns L decWeight a b site t

/--
[ons_detWalkRoot_scale_chain_zero_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_detWalkRoot_scale_chain_zero_affine_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {t : ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentryAux : ∀ d₂ d₁, ‖ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight s((site, 0), ons_dartRev L (site, 0)) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 0) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_maskMatrix ({(site, 0), ons_dartRev L (site, 0)} : Finset (ons_Dart L)) (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - t * ∑' s, ons_firstReturnWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (site, 0) (ons_dartRev L (site, 0)) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scale_chain_zero_affine L decWeight a b site t q hq hentryAux hsmall hcard

/--
[ons_detWalkRoot_scale_chain_two_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalEndpoint.lean)
-/
@[path]
private lemma ons_detWalkRoot_scale_chain_two_affine_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {t : ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentryAux : ∀ d₂ d₁, ‖ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight s((site, 3), ons_dartRev L (site, 3)) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 2) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_maskMatrix ({(site, 3), ons_dartRev L (site, 3)} : Finset (ons_Dart L)) (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - t * ∑' s, ons_firstReturnWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (site, 3) (ons_dartRev L (site, 3)) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scale_chain_two_affine L decWeight a b site t q hq hentryAux hsmall hcard


-- created on 2026-10-23
