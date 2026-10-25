import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSquarefree
open StatMech StatMech.Onsager


/--
[ons_not_isSquarefreeExponent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSquarefree.lean)
-/
@[path]
private lemma ons_not_isSquarefreeExponent_iff_eq
  {m : E →₀ ℕ} :
-- imply
  ¬ ons_IsSquarefreeExponent m ↔ ∃ edge, 2 ≤ m edge := by
-- proof
  apply StatMech.Onsager.ons_not_isSquarefreeExponent_iff m

/--
[ons_decoratedFormalKacWardIdentity_of_nonsquarefree_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSquarefree.lean)
-/
@[path]
private lemma ons_decoratedFormalKacWardIdentity_of_nonsquarefree_vanishes_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hvanish : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ), ¬ ons_IsSquarefreeExponent m → MvPowerSeries.coeff m (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
-- imply
  ons_decoratedFormalKacWardIdentity L := by
-- proof
  apply StatMech.Onsager.ons_decoratedFormalKacWardIdentity_of_nonsquarefree_vanishes L hvanish

/--
[ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSquarefree.lean)
-/
@[path]
private lemma ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hvanish : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ) (edge : ons_DecEdge L), 2 ≤ m edge → MvPowerSeries.coeff m (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
-- imply
  ons_decoratedFormalKacWardIdentity L := by
-- proof
  apply StatMech.Onsager.ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes L hvanish


-- created on 2026-10-23
