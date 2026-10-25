import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2
open StatMech StatMech.Onsager


/--
[norm_ons_restrictEdgeWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean)
-/
@[path]
private lemma norm_ons_restrictEdgeWeight_le_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {S : Finset (Sym2 (ZMod L × ZMod L))}
  {q : ℝ}
  (edge)
-- given
  (hq : 0 ≤ q)
  (hweight : ∀ edge, ‖weight edge‖ ≤ q) :
-- imply
  ‖ons_restrictEdgeWeight weight S edge‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_ons_restrictEdgeWeight_le weight S q hq hweight

/--
[ons_scale_restrict_insert_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean)
-/
@[path]
private lemma ons_scale_restrict_insert_one_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {S : Finset (Sym2 (ZMod L × ZMod L))}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  ons_scaleEdgeWeight (ons_restrictEdgeWeight weight (insert edge S)) edge 1 = ons_restrictEdgeWeight weight (insert edge S) := by
-- proof
  apply StatMech.Onsager.ons_scale_restrict_insert_one weight S edge

/--
[ons_scale_restrict_insert_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean)
-/
@[path]
private lemma ons_scale_restrict_insert_zero_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {S : Finset (Sym2 (ZMod L × ZMod L))}
  {edge : Sym2 (ZMod L × ZMod L)}
-- given
  (hedge : edge ∉ S) :
-- imply
  ons_scaleEdgeWeight (ons_restrictEdgeWeight weight (insert edge S)) edge 0 = ons_restrictEdgeWeight weight S := by
-- proof
  apply StatMech.Onsager.ons_scale_restrict_insert_zero weight S edge hedge

/--
[ons_KWmatWeightedPhase_restrict_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_restrict_edgeFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v : ℂ} :
-- imply
  ons_KWmatWeightedPhase L (ons_restrictEdgeWeight weight (onsTorusGraph L).edgeFinset) omega u v = ons_KWmatWeightedPhase L weight omega u v := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_restrict_edgeFinset L weight omega u v

/--
[ons_weightedSpinCharacterSum_restrict_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean)
-/
@[path]
private lemma ons_weightedSpinCharacterSum_restrict_edgeFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L (ons_restrictEdgeWeight weight (onsTorusGraph L).edgeFinset) a b = ons_weightedSpinCharacterSum L weight a b := by
-- proof
  apply StatMech.Onsager.ons_weightedSpinCharacterSum_restrict_edgeFinset L weight a b

/--
[ons_weightedRootIdentity_of_edgeCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean)
-/
@[path]
private lemma ons_weightedRootIdentity_of_edgeCoefficient_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hcoeff : ons_weightedEdgeCoefficientIdentity L) :
-- imply
  ons_weightedRootIdentity L := by
-- proof
  apply StatMech.Onsager.ons_weightedRootIdentity_of_edgeCoefficient L hcoeff


-- created on 2026-10-23
