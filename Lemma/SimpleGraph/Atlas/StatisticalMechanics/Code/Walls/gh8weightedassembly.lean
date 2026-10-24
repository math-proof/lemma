import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gh8weightedassembly
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh8_weighted_drop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean)
-/
@[path]
private lemma gh8_weighted_drop_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {wgtA diffA : Finset ι → ℝ}
-- given
  (hwgt : ∀ A, 0 ≤ wgtA A)
  (hdiff : ∀ A, 0 ≤ diffA A) :
-- imply
  0 ≤ ∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A := by
-- proof
  apply StatMech.Walls.gh8_weighted_drop_nonneg ends m V₁ V₂ u wgtA diffA hwgt hdiff

/--
[gh8_eq22_decomp_of_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean)
-/
@[path]
private lemma gh8_eq22_decomp_of_weighted_eq
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
  {u u' : W}
-- given
  (β h : ℝ)
  (heq22 : gh8_weighted_eq22 G β h o x y ends m u u') :
-- imply
  gh3_eq22_decomposition G β h o x y := by
-- proof
  apply StatMech.Walls.gh8_eq22_decomp_of_weighted G β h o x y ends m u u' heq22

/--
[gh8_weighted_gks_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean)
-/
@[path]
private lemma gh8_weighted_gks_drop_eq
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
  {u u' : W}
  {surv : ℝ}
-- given
  (β h : ℝ)
  (heq22 : ∃ (V₁ V₂ V₁' V₂' : Finset W) (wgtA diffA wgtB diffB : Finset ι → ℝ), (∀ A, 0 ≤ wgtA A) ∧ (∀ A, 0 ≤ diffA A) ∧ (∀ B, 0 ≤ wgtB B) ∧ (∀ B, 0 ≤ diffB B) ∧ eg_ursell3 G β h o x y = surv - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A) - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
-- imply
  eg_ursell3 G β h o x y ≤ surv := by
-- proof
  apply StatMech.Walls.gh8_weighted_gks_drop G β h o x y ends m u u' heq22

/--
[gh8_ghs_of_weighted_eq22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean)
-/
@[path]
private lemma gh8_ghs_of_weighted_eq22_eq
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
  {u u' : W}
-- given
  (β h : ℝ)
  (heq22 : gh8_weighted_eq22 G β h o x y ends m u u') :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh8_ghs_of_weighted_eq22 G β h o x y ends m u u' heq22

/--
[gh8_lemma1_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean)
-/
@[path]
private lemma gh8_lemma1_covariance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β) :
-- imply
  StatMech.Ising.cov2 G β h i j * StatMech.Ising.cov2 G β h j k ≤ StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G β h) (fun s => StatMech.Ising.spin s j) * StatMech.Ising.cov2 G β h i k := by
-- proof
  apply StatMech.Walls.gh8_lemma1_covariance G β h hβ i j k

/--
[gh8_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean)
-/
@[path]
private lemma gh8_status_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh8_status

/--
[gh8_smallmodel_check](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean)
-/
@[path]
private lemma gh8_smallmodel_check_eq
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
  {u u' : W}
-- given
  (β h : ℝ)
  (hzero : eg_ursell3 G β h o x y = 0) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh8_smallmodel_check G β h o x y ends m u u' hzero


-- created on 2026-10-23
