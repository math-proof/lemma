import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights
open StatMech StatMech.Onsager


/--
[ons_decInterpolatedWeight_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decInterpolatedWeight_one_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ} :
-- imply
  ons_decInterpolatedWeight weight 1 = ons_decSpecializedWeight weight := by
-- proof
  apply StatMech.Onsager.ons_decInterpolatedWeight_one weight

/--
[ons_decSpecializedWeight_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decSpecializedWeight_external_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {d : ons_Dart L} :
-- imply
  ons_decSpecializedWeight weight s(d, ons_dartRev L d) = weight (ons_portEdge L d) := by
-- proof
  apply StatMech.Onsager.ons_decSpecializedWeight_external L weight d

/--
[ons_decInterpolatedWeight_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decInterpolatedWeight_external_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {t : ℂ}
  {d : ons_Dart L} :
-- imply
  ons_decInterpolatedWeight weight t s(d, ons_dartRev L d) = weight (ons_portEdge L d) := by
-- proof
  apply StatMech.Onsager.ons_decInterpolatedWeight_external L weight t d

/--
[ons_decChainEdge_mem_decGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decChainEdge_mem_decGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_decChainEdge site i ∈ (ons_decGraph L).edgeFinset := by
-- proof
  apply StatMech.Onsager.ons_decChainEdge_mem_decGraph L site i

/--
[ons_decChainEdge_not_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decChainEdge_not_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ¬ ons_decIsExternal (ons_decChainEdge site i) := by
-- proof
  apply StatMech.Onsager.ons_decChainEdge_not_external L site i

/--
[ons_decSpecializedWeight_chainEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decSpecializedWeight_chainEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_decSpecializedWeight weight (ons_decChainEdge site i) = 1 := by
-- proof
  apply StatMech.Onsager.ons_decSpecializedWeight_chainEdge L weight site i

/--
[ons_decInterpolatedWeight_chainEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decInterpolatedWeight_chainEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {t : ℂ}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_decInterpolatedWeight weight t (ons_decChainEdge site i) = t := by
-- proof
  apply StatMech.Onsager.ons_decInterpolatedWeight_chainEdge L weight t site i

/--
[norm_ons_decInterpolatedWeight_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma norm_ons_decInterpolatedWeight_le_one_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {q : ℝ}
  {t : ℂ}
  {edge : Sym2 (ons_Dart L)}
-- given
  (hq1 : q ≤ 1)
  (hweight : ∀ edge, ‖weight edge‖ ≤ q)
  (ht : ‖t‖ ≤ 1) :
-- imply
  ‖ons_decInterpolatedWeight weight t edge‖ ≤ 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_decInterpolatedWeight_le_one weight q hq1 hweight t ht edge

/--
[ons_decTransitionWeight_specialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decTransitionWeight_specialized_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {d₂ d₁ : ons_Dart L} :
-- imply
  ons_decTransitionWeight L (ons_decSpecializedWeight weight) d₂ d₁ = weight (ons_portEdge L d₁) := by
-- proof
  apply StatMech.Onsager.ons_decTransitionWeight_specialized L weight d₂ d₁

/--
[ons_KWmatDecorationWeightedPhase_specialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_specialized_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v : ℂ} :
-- imply
  ons_KWmatDecorationWeightedPhase L (ons_decSpecializedWeight weight) omega u v = ons_KWmatWeightedPhase L weight omega u v := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_specialized L weight omega u v

/--
[norm_ons_decTransitionWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma norm_ons_decTransitionWeight_le_eq
  {L : ℕ}
  {decWeight : Sym2 (ons_Dart L) → ℂ}
  {q : ℝ}
  {d₂ d₁ : ons_Dart L}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q) :
-- imply
  ‖ons_decTransitionWeight L decWeight d₂ d₁‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_ons_decTransitionWeight_le L decWeight q hq hall hext d₂ d₁

/--
[norm_ons_KWmatDecorationWeightedPhase_entry_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma norm_ons_KWmatDecorationWeightedPhase_entry_le_eq
  {L : ℕ}
  {decWeight : Sym2 (ons_Dart L) → ℂ}
  {a b : Fin 2}
  {q : ℝ}
  {d₂ d₁ : ons_Dart L}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q) :
-- imply
  ‖ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_ons_KWmatDecorationWeightedPhase_entry_le L decWeight a b q hq hall hext d₂ d₁

/--
[ons_KWmatDecorationWeightedPhase_detWalkRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_detWalkRoot_sq_eq
  {L : ℕ}
  [NeZero L]
  {decWeight : Sym2 (ons_Dart L) → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) ^ 2 = (1 - ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_detWalkRoot_sq L decWeight a b q hq hall hext hsmall

/--
[ons_decoratedFullWeight_specialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decoratedFullWeight_specialized_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  (∏ edge ∈ D.1, ons_decSpecializedWeight weight edge) = ∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge := by
-- proof
  apply StatMech.Onsager.ons_decoratedFullWeight_specialized L weight D

/--
[ons_decoratedFullWeightedSpinSum_specialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean)
-/
@[path]
private lemma ons_decoratedFullWeightedSpinSum_specialized_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2} :
-- imply
  ons_decoratedFullWeightedSpinSum L (ons_decSpecializedWeight weight) a b = ons_weightedSpinCharacterSum L weight a b := by
-- proof
  apply StatMech.Onsager.ons_decoratedFullWeightedSpinSum_specialized L weight a b


-- created on 2026-10-23
