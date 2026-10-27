import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
open MeasureTheory StatMech StatMech.FrontierB


/--
[boolSupport_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean)
-/
@[path]
private lemma boolSupport_injective_eq
  [Fintype I]
  [DecidableEq I] :
-- imply
  Function.Injective (boolSupport : (I → Bool) → Finset I) := by
-- proof
  apply StatMech.FrontierB.boolSupport_injective

/--
[mem_boolAvoid_compl_support_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean)
-/
@[path]
private lemma mem_boolAvoid_compl_support_iff_eq
  [Fintype I]
  [DecidableEq I]
  {a b : I → Bool} :
-- imply
  a ∈ boolAvoid (Finset.univ \ boolSupport b) ↔ boolSupport a ⊆ boolSupport b := by
-- proof
  apply StatMech.FrontierB.mem_boolAvoid_compl_support_iff a b

/--
[boolAvoid_mass_eq_apply_add_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean)
-/
@[path]
private lemma boolAvoid_mass_eq_apply_add_lower_eq
  [Fintype I]
  [DecidableEq I]
  {p : PMF (I → Bool)}
  {b : I → Bool} :
-- imply
  p.toMeasure (boolAvoid (Finset.univ \ boolSupport b)) = p b + ∑ a ∈ boolLower b, p a := by
-- proof
  apply StatMech.FrontierB.boolAvoid_mass_eq_apply_add_lower p b

/--
[PMF.ext_of_boolAvoid_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean)
-/
@[path]
private lemma ext_of_boolAvoid_eq_eq
  [Fintype I]
  [DecidableEq I]
  {p q : PMF (I → Bool)}
-- given
  (h : ∀ T : Finset I, p.toMeasure (boolAvoid T) = q.toMeasure (boolAvoid T)) :
-- imply
  p = q := by
-- proof
  apply StatMech.FrontierB.PMF.ext_of_boolAvoid_eq h

/--
[finiteParityKernel_eq_zero_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean)
-/
@[path]
private lemma finiteParityKernel_eq_zero_of_ne_eq
  [DecidableEq E]
  {S : Finset E}
  {beta : ℝ}
  {odd : ↑S → Bool}
  {a : ↑S → ℕ}
-- given
  (hne : odd ≠ currentLocalParity a) :
-- imply
  finiteParityKernel S beta odd a = 0 := by
-- proof
  apply StatMech.FrontierB.finiteParityKernel_eq_zero_of_ne S beta odd a hne

/--
[finiteParityPMF_eq_zero_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean)
-/
@[path]
private lemma finiteParityPMF_eq_zero_of_ne_eq
  [DecidableEq E]
  {S : Finset E}
  {beta : ℝ}
  {odd : ↑S → Bool}
  {a : ↑S → ℕ}
-- given
  (hbeta : 0 < beta)
  (hne : odd ≠ currentLocalParity a) :
-- imply
  finiteParityPMF S beta hbeta odd a = 0 := by
-- proof
  apply StatMech.FrontierB.finiteParityPMF_eq_zero_of_ne S beta hbeta odd a hne

/--
[bind_finiteParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean)
-/
@[path]
private lemma bind_finiteParityPMF_apply_eq
  [DecidableEq E]
  {S : Finset E}
  {beta : ℝ}
  {p : PMF (↑S → Bool)}
  {a : ↑S → ℕ}
-- given
  (hbeta : 0 < beta) :
-- imply
  p.bind (finiteParityPMF S beta hbeta) a = p (currentLocalParity a) * finiteParityPMF S beta hbeta (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.bind_finiteParityPMF_apply S beta hbeta p a


-- created on 2026-10-23
