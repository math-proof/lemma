import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.FirstReturnScale
open StatMech StatMech.Onsager


/--
[ons_edgeWeight_scale_to_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FirstReturnScale.lean)
-/
@[path]
private lemma ons_edgeWeight_scale_to_last_eq
  [DecidableEq E]
  {S : Finset E}
  {t : ℂ}
  {Lambda : Matrix E E ℂ}
  {a e : E}
  {interior : List E}
-- given
  (he : e ∈ S)
  (hint : ∀ x ∈ interior, x ∉ S) :
-- imply
  ons_edgeWeight (ons_scaleColumns S t Lambda) (a :: interior ++ [e]) = t * ons_edgeWeight Lambda (a :: interior ++ [e]) := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_scale_to_last S t Lambda a e interior he hint

/--
[ons_firstReturnWeight_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FirstReturnScale.lean)
-/
@[path]
private lemma ons_firstReturnWeight_scale_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
  {t : ℂ}
  {s : List E} :
-- imply
  ons_firstReturnWeight (ons_scaleColumns ({e, r} : Finset E) t Lambda) e r s = t * ons_firstReturnWeight Lambda e r s := by
-- proof
  apply StatMech.Onsager.ons_firstReturnWeight_scale Lambda e r t s

/--
[ons_tsum_firstReturnWeight_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FirstReturnScale.lean)
-/
@[path]
private lemma ons_tsum_firstReturnWeight_scale_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
  {t : ℂ} :
-- imply
  (∑' s, ons_firstReturnWeight (ons_scaleColumns ({e, r} : Finset E) t Lambda) e r s) = t * ∑' s, ons_firstReturnWeight Lambda e r s := by
-- proof
  apply StatMech.Onsager.ons_tsum_firstReturnWeight_scale Lambda e r t


-- created on 2026-10-23
