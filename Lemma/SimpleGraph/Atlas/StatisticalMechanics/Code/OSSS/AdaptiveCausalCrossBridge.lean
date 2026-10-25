import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalCrossBridge
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[realizedList_extendDecisionTreeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossBridge.lean)
-/
@[path]
private lemma realizedList_extendDecisionTreeAt_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E} :
-- imply
  realizedList (extendDecisionTreeAt t T known R) base = realizedList (extendDecisionTree T known R) base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_extendDecisionTreeAt t T known base R

/--
[realizedList_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossBridge.lean)
-/
@[path]
private lemma realizedList_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {phase : Option ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E} :
-- imply
  realizedList (extendDecisionTreeTriple phase T known R).leftOrder base = realizedList (extendDecisionTree T known R) base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_extendDecisionTreeTriple phase T known base R

/--
[realizedEquiv_apply_eq_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossBridge.lean)
-/
@[path]
private lemma realizedEquiv_apply_eq_getElem_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {i : Fin (Fintype.card E)} :
-- imply
  realizedEquiv S base i = (realizedList S base)[(i : ℕ)]'(by rw [realizedList_length] simpa using i.isLt) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedEquiv_apply_eq_getElem S base i

/--
[realizedEquiv_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossBridge.lean)
-/
@[path]
private lemma realizedEquiv_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {phase : Option ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E} :
-- imply
  realizedEquiv (extendDecisionTreeTriple phase T known (Finset.univ : Finset E)).leftOrder base = realizedEquiv (extendDecisionTree T known Finset.univ) base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedEquiv_extendDecisionTreeTriple phase T known base

/--
[idxOf_flip_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossBridge.lean)
-/
@[path]
private lemma idxOf_flip_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
  {e : E}
-- given
  (he : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base e = .flip) :
-- imply
  (realizedList (extendDecisionTreeTriple (some t) T known R).leftOrder base).idxOf e = t := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.idxOf_flip_extendDecisionTreeTriple t T known base R e he

/--
[realizedEquiv_symm_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossBridge.lean)
-/
@[path]
private lemma realizedEquiv_symm_flip_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {e : E}
-- given
  (he : tripleModeAt (extendDecisionTreeTriple (some t) T known (Finset.univ : Finset E)) base e = .flip) :
-- imply
  ((realizedEquiv (extendDecisionTreeTriple (some t) T known Finset.univ).leftOrder base).symm e : ℕ) = t := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedEquiv_symm_flip t T known base e he

/--
[cross_flip_atom_sum_eq_flipCrossTripleProb_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalCrossBridge.lean)
-/
@[path]
private lemma cross_flip_atom_sum_eq_flipCrossTripleProb_sum_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {seed : ConfigSpace E}
  {e : E}
  {S : TripleOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ConfigSpace E → ℝ} :
-- imply
  (∑ base, (if tripleModeAt S base e = .flip then 1 else 0) * (∑ left, ∑ right, g left right * crossTripleJointProb mu ∅ base left right S)) = ∑ left, ∑ right, g left right * flipCrossTripleProb mu ∅ seed left right e S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.cross_flip_atom_sum_eq_flipCrossTripleProb_sum mu seed e S g


-- created on 2026-10-23
