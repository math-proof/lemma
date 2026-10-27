import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalRootFlip
open StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[cExp_coord_eq_condProbBit_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalRootFlip.lean)
-/
@[path]
private lemma cExp_coord_eq_condProbBit_true_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed : ConfigSpace E}
  {q : E} :
-- imply
  Lindeberg.cExp mu F (Lindeberg.coord q) seed = condProbBit mu F seed q true := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.cExp_coord_eq_condProbBit_true mu F seed q

/--
[baseSum_coord_mul_crossTripleProb_right_rootFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalRootFlip.lean)
-/
@[path]
private lemma baseSum_coord_mul_crossTripleProb_right_rootFlip_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left seed : ConfigSpace E}
  {R : Finset E}
  {q : E}
  {closed opened : TripleOrder (R.erase q)}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hq : q ∈ R)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun right => Lindeberg.coord q right * crossTripleProb mu F base left right (.node q hq .flip closed opened)) = condProbBit mu F seed q true * targetProb mu F base left (TripleOrder.leftOrder (.node q hq .flip closed opened)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_coord_mul_crossTripleProb_right_rootFlip mu hpos F base left seed q hq closed opened hR

/--
[baseSum_coord_mul_crossTripleProb_right_rootFlip_eq_cExp_mul_condMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalRootFlip.lean)
-/
@[path]
private lemma baseSum_coord_mul_crossTripleProb_right_rootFlip_eq_cExp_mul_condMass_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {F : Finset E}
  {driver left rightSeed : ConfigSpace E}
  {R : Finset E}
  {q : E}
  {closed opened : TripleOrder (R.erase q)}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hq : q ∈ R)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F rightSeed (fun right => Lindeberg.coord q right * crossTripleProb mu F driver left right (.node q hq .flip closed opened)) = Lindeberg.cExp mu F (Lindeberg.coord q) rightSeed * condMass mu F left left := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_coord_mul_crossTripleProb_right_rootFlip_eq_cExp_mul_condMass mu hpos F driver left rightSeed q hq closed opened hR

/--
[baseSum_coord_mul_crossTripleProb_left_rootFlip_eq_cExp_mul_condMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalRootFlip.lean)
-/
@[path]
private lemma baseSum_coord_mul_crossTripleProb_left_rootFlip_eq_cExp_mul_condMass_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {F : Finset E}
  {driver right leftSeed : ConfigSpace E}
  {R : Finset E}
  {q : E}
  {closed opened : TripleOrder (R.erase q)}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hq : q ∈ R)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F leftSeed (fun left => Lindeberg.coord q left * crossTripleProb mu F driver left right (.node q hq .flip closed opened)) = Lindeberg.cExp mu F (Lindeberg.coord q) leftSeed * condMass mu F right right := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_coord_mul_crossTripleProb_left_rootFlip_eq_cExp_mul_condMass mu hpos F driver right leftSeed q hq closed opened hR


-- created on 2026-10-23
