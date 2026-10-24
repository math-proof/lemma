import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gh6attach
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh6_restricted_weight_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh6attach.lean)
-/
@[path]
private lemma gh6_restricted_weight_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {Ac : Finset V}
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  gc15_tpsum G β (StatMech.Sharpness.couplingIn J Ac) m A B = (gc85b_pcount (endsM G m) univ A B : ℝ) * weight G β (StatMech.Sharpness.couplingIn J Ac) (ofEdgeFun G m) := by
-- proof
  apply StatMech.Walls.gh6_restricted_weight_bridge G β J Ac m A B

/--
[gh6_restricted_expectation_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh6attach.lean)
-/
@[path]
private lemma gh6_restricted_expectation_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {Ac : Finset V}
  {k l : V} :
-- imply
  StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J Ac) {k, l} = StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) {k, l} / StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) ∅ := by
-- proof
  apply StatMech.Walls.gh6_restricted_expectation_ratio G β J Ac k l

/--
[gh6_expectation_times_Z_eq_currentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh6attach.lean)
-/
@[path]
private lemma gh6_expectation_times_Z_eq_currentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {Ac : Finset V}
  {k l : V}
-- given
  (hZ : StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) ∅ ≠ 0) :
-- imply
  StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J Ac) {k, l} * StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) ∅ = StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) {k, l} := by
-- proof
  apply StatMech.Walls.gh6_expectation_times_Z_eq_currentSum G β J Ac k l hZ

/--
[gh6_weighted_attachment_reduces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh6attach.lean)
-/
@[path]
private lemma gh6_weighted_attachment_reduces_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ V₁' V₂' : Finset W}
  {u u' : W}
  {wgtA diffA wgtB diffB : Finset ι → ℝ}
  {surv : ℝ}
-- given
  (β h : ℝ)
  (hwgtA : ∀ A, 0 ≤ wgtA A)
  (hdiffA : ∀ A, 0 ≤ diffA A)
  (hwgtB : ∀ B, 0 ≤ wgtB B)
  (hdiffB : ∀ B, 0 ≤ diffB B)
  (hident : eg_ursell3 G β h o x y = surv - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A) - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
-- imply
  gh3_eq22_decomposition G β h o x y := by
-- proof
  apply StatMech.Walls.gh6_weighted_attachment_reduces G β h o x y ends m V₁ V₂ V₁' V₂' u u' wgtA diffA wgtB diffB hwgtA hdiffA hwgtB hdiffB surv hident

/--
[gh6_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh6attach.lean)
-/
@[path]
private lemma gh6_status_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh6_status


-- created on 2026-10-23
