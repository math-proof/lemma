import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.AdaptiveCausalWeightedMoments
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[flipCrossTripleProb_right_coord_marginal_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalWeightedMoments.lean)
-/
@[path]
private lemma flipCrossTripleProb_right_coord_marginal_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {F : Finset E}
  {driver left rightSeed : ConfigSpace E}
  {z : E}
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F rightSeed (fun right => Lindeberg.coord z right * flipCrossTripleProb mu F driver left right z (extendDecisionTreeTriple (some t) T known R)) = Lindeberg.cExp mu F (Lindeberg.coord z) rightSeed * condMass mu F left left * flipBaseProb mu F driver z (extendDecisionTreeTriple (some t) T known R) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipCrossTripleProb_right_coord_marginal_extendDecisionTreeTriple mu hpos F driver left rightSeed z t T known R hR

/--
[flipCrossTripleProb_left_coord_marginal_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalWeightedMoments.lean)
-/
@[path]
private lemma flipCrossTripleProb_left_coord_marginal_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {F : Finset E}
  {driver leftSeed right : ConfigSpace E}
  {z : E}
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F leftSeed (fun left => Lindeberg.coord z left * flipCrossTripleProb mu F driver left right z (extendDecisionTreeTriple (some t) T known R)) = Lindeberg.cExp mu F (Lindeberg.coord z) leftSeed * condMass mu F right right * flipBaseProb mu F driver z (extendDecisionTreeTriple (some t) T known R) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipCrossTripleProb_left_coord_marginal_extendDecisionTreeTriple mu hpos F driver leftSeed right z t T known R hR

/--
[sum_coord_mul_flipCrossTripleProb_right_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalWeightedMoments.lean)
-/
@[path]
private lemma sum_coord_mul_flipCrossTripleProb_right_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {driver left rightSeed : ConfigSpace E}
  {z : E}
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hmu : ∑ omega, mu omega = 1) :
-- imply
  (∑ right, Lindeberg.coord z right * flipCrossTripleProb mu ∅ driver left right z (extendDecisionTreeTriple (some t) T known Finset.univ)) = Lindeberg.mean mu (Lindeberg.coord z) * mu left * flipBaseProb mu ∅ driver z (extendDecisionTreeTriple (some t) T known Finset.univ) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_coord_mul_flipCrossTripleProb_right_extendDecisionTreeTriple mu hpos hmu driver left rightSeed z t T known

/--
[sum_coord_mul_flipCrossTripleProb_left_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalWeightedMoments.lean)
-/
@[path]
private lemma sum_coord_mul_flipCrossTripleProb_left_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {driver leftSeed right : ConfigSpace E}
  {z : E}
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hmu : ∑ omega, mu omega = 1) :
-- imply
  (∑ left, Lindeberg.coord z left * flipCrossTripleProb mu ∅ driver left right z (extendDecisionTreeTriple (some t) T known Finset.univ)) = Lindeberg.mean mu (Lindeberg.coord z) * mu right * flipBaseProb mu ∅ driver z (extendDecisionTreeTriple (some t) T known Finset.univ) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_coord_mul_flipCrossTripleProb_left_extendDecisionTreeTriple mu hpos hmu driver leftSeed right z t T known

/--
[flipCrossTripleProb_structured_orientations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalWeightedMoments.lean)
-/
@[path]
private lemma flipCrossTripleProb_structured_orientations_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {seed : ConfigSpace E}
  {t : ℕ}
  {z : E}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hmu : ∑ omega, mu omega = 1) :
-- imply
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E) (∑ left, ∑ right, T.evalR left * Lindeberg.coord z right * flipCrossTripleProb mu ∅ seed left right z S) = Lindeberg.mean mu T.evalR * Lindeberg.mean mu (Lindeberg.coord z) * flipBaseProb mu ∅ seed z S ∧ (∑ left, ∑ right, T.evalR right * Lindeberg.coord z left * flipCrossTripleProb mu ∅ seed left right z S) = Lindeberg.mean mu T.evalR * Lindeberg.mean mu (Lindeberg.coord z) * flipBaseProb mu ∅ seed z S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipCrossTripleProb_structured_orientations mu hpos hmu T seed t z


-- created on 2026-10-23
