import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalMoments
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[flipTripleProb_left_marginal_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalMoments.lean)
-/
@[path]
private lemma flipTripleProb_left_marginal_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → Real}
  {F : Finset E}
  {driver leftSeed right : ConfigSpace E}
  {z : E}
  {t : Nat}
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F leftSeed (fun left => flipTripleProb mu F driver left right z (extendDecisionTreeTriple (some t) T known R)) = condMass mu F right right * flipBaseProb mu F driver z (extendDecisionTreeTriple (some t) T known R) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipTripleProb_left_marginal_extendDecisionTreeTriple mu hpos F driver leftSeed right z t T known R hR

/--
[sum_flipTripleProb_right_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalMoments.lean)
-/
@[path]
private lemma sum_flipTripleProb_right_extendDecisionTreeTriple_eq
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
  (∑ right, flipTripleProb mu ∅ driver left right z (extendDecisionTreeTriple (some t) T known Finset.univ)) = mu left * flipBaseProb mu ∅ driver z (extendDecisionTreeTriple (some t) T known Finset.univ) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_flipTripleProb_right_extendDecisionTreeTriple mu hpos hmu driver left rightSeed z t T known

/--
[sum_flipTripleProb_left_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalMoments.lean)
-/
@[path]
private lemma sum_flipTripleProb_left_extendDecisionTreeTriple_eq
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
  (∑ left, flipTripleProb mu ∅ driver left right z (extendDecisionTreeTriple (some t) T known Finset.univ)) = mu right * flipBaseProb mu ∅ driver z (extendDecisionTreeTriple (some t) T known Finset.univ) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_flipTripleProb_left_extendDecisionTreeTriple mu hpos hmu driver leftSeed right z t T known

/--
[flipCrossTripleProb_right_marginal_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalMoments.lean)
-/
@[path]
private lemma flipCrossTripleProb_right_marginal_extendDecisionTreeTriple_eq
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
  baseSum F rightSeed (fun right => flipCrossTripleProb mu F driver left right z (extendDecisionTreeTriple (some t) T known R)) = condMass mu F left left * flipBaseProb mu F driver z (extendDecisionTreeTriple (some t) T known R) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipCrossTripleProb_right_marginal_extendDecisionTreeTriple mu hpos F driver left rightSeed z t T known R hR

/--
[flipCrossTripleProb_left_marginal_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalMoments.lean)
-/
@[path]
private lemma flipCrossTripleProb_left_marginal_extendDecisionTreeTriple_eq
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
  baseSum F leftSeed (fun left => flipCrossTripleProb mu F driver left right z (extendDecisionTreeTriple (some t) T known R)) = condMass mu F right right * flipBaseProb mu F driver z (extendDecisionTreeTriple (some t) T known R) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipCrossTripleProb_left_marginal_extendDecisionTreeTriple mu hpos F driver leftSeed right z t T known R hR

/--
[sum_flipCrossTripleProb_right_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalMoments.lean)
-/
@[path]
private lemma sum_flipCrossTripleProb_right_extendDecisionTreeTriple_eq
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
  (∑ right, flipCrossTripleProb mu ∅ driver left right z (extendDecisionTreeTriple (some t) T known Finset.univ)) = mu left * flipBaseProb mu ∅ driver z (extendDecisionTreeTriple (some t) T known Finset.univ) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_flipCrossTripleProb_right_extendDecisionTreeTriple mu hpos hmu driver left rightSeed z t T known

/--
[sum_flipCrossTripleProb_left_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalMoments.lean)
-/
@[path]
private lemma sum_flipCrossTripleProb_left_extendDecisionTreeTriple_eq
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
  (∑ left, flipCrossTripleProb mu ∅ driver left right z (extendDecisionTreeTriple (some t) T known Finset.univ)) = mu right * flipBaseProb mu ∅ driver z (extendDecisionTreeTriple (some t) T known Finset.univ) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_flipCrossTripleProb_left_extendDecisionTreeTriple mu hpos hmu driver leftSeed right z t T known


-- created on 2026-10-23
