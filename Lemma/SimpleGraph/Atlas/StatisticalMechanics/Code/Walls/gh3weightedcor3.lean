import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gh3weightedcor3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh3_gks_drop_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh3weightedcor3.lean)
-/
@[path]
private lemma gh3_gks_drop_pair_eq
  [Fintype V]
  [DecidableEq V]
  {E₁ E₂ : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {k l : V}
-- given
  (hf : V → ℝ)
  (hsub : E₁ ⊆ E₂)
  (hJ : ∀ e ∈ E₂, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) :
-- imply
  StatMech.Sharpness.expJ E₁ J hf (StatMech.Ising.spinProd {k, l}) ≤ StatMech.Sharpness.expJ E₂ J hf (StatMech.Ising.spinProd {k, l}) := by
-- proof
  apply StatMech.Walls.gh3_gks_drop_pair E₁ E₂ J hf hsub hJ hhf hdiag k l

/--
[gh3_gks_drop_diff_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh3weightedcor3.lean)
-/
@[path]
private lemma gh3_gks_drop_diff_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E₁ E₂ : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {k l : V}
-- given
  (hf : V → ℝ)
  (hsub : E₁ ⊆ E₂)
  (hJ : ∀ e ∈ E₂, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) :
-- imply
  0 ≤ StatMech.Sharpness.expJ E₂ J hf (StatMech.Ising.spinProd {k, l}) - StatMech.Sharpness.expJ E₁ J hf (StatMech.Ising.spinProd {k, l}) := by
-- proof
  apply StatMech.Walls.gh3_gks_drop_diff_nonneg E₁ E₂ J hf hsub hJ hhf hdiag k l

/--
[gh3_dropped_term_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh3weightedcor3.lean)
-/
@[path]
private lemma gh3_dropped_term_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {mass diff : ℝ}
-- given
  (hmass : 0 ≤ mass)
  (hdiff : 0 ≤ diff) :
-- imply
  0 ≤ 2 * mass * diff := by
-- proof
  apply StatMech.Walls.gh3_dropped_term_nonneg mass diff hmass hdiff

/--
[gh3_gks_drop_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh3weightedcor3.lean)
-/
@[path]
private lemma gh3_gks_drop_step_eq
  [Fintype V]
  [DecidableEq V]
  {LHS SURV dropA dropB : ℝ}
-- given
  (hdecomp : LHS = SURV - 2 * dropA - 2 * dropB)
  (hA : 0 ≤ dropA)
  (hB : 0 ≤ dropB) :
-- imply
  LHS ≤ SURV := by
-- proof
  apply StatMech.Walls.gh3_gks_drop_step LHS SURV dropA dropB hdecomp hA hB

/--
[gh3_weighted_cor3_via_gks_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh3weightedcor3.lean)
-/
@[path]
private lemma gh3_weighted_cor3_via_gks_drop_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hdecomp : gh3_eq22_decomposition G β h o x y)
  (hfinish : ∀ surv : ℝ, eg_ursell3 G β h o x y ≤ surv → gh3_lemma1_finish G β h o x y surv) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh3_weighted_cor3_via_gks_drop G β h o x y hdecomp hfinish

/--
[gh3_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh3weightedcor3.lean)
-/
@[path]
private lemma gh3_status_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh3_status


-- created on 2026-10-23
