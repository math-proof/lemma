import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SpinWeightedAffine
open StatMech StatMech.Onsager


/--
[ons_prod_scaleEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedAffine.lean)
-/
@[path]
private lemma ons_prod_scaleEdgeWeight_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {edge : Sym2 (ZMod L × ZMod L)}
  {t : ℂ}
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  (∏ f ∈ F, ons_scaleEdgeWeight weight edge t f) = if edge ∈ F then t * ∏ f ∈ F, weight f else ∏ f ∈ F, weight f := by
-- proof
  apply StatMech.Onsager.ons_prod_scaleEdgeWeight weight edge t F

/--
[ons_weightedSpinCharacterSum_scaleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedAffine.lean)
-/
@[path]
private lemma ons_weightedSpinCharacterSum_scaleEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
  {edge : Sym2 (ZMod L × ZMod L)}
  {t : ℂ} :
-- imply
  ons_weightedSpinCharacterSum L (ons_scaleEdgeWeight weight edge t) a b = ons_weightedSpinCharacterSum L (ons_scaleEdgeWeight weight edge 0) a b + t * ons_weightedSpinEdgeCoefficient L weight a b edge := by
-- proof
  apply StatMech.Onsager.ons_weightedSpinCharacterSum_scaleEdge L weight a b edge t


-- created on 2026-10-23
