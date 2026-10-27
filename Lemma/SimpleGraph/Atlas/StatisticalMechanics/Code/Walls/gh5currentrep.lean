import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gh5currentrep.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh5_sources_union_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_sources_union_of_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S T : Finset ι}
-- given
  (h : Disjoint S T) :
-- imply
  sources ends (S ∪ T) = sources ends S ∆ sources ends T := by
-- proof
  apply StatMech.Walls.gh5_sources_union_of_disjoint ends h

/--
[gh5_compMass_eq_complMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_compMass_eq_complMass_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {A : Finset ι}
-- given
  (hAm : A ⊆ m) :
-- imply
  gh4_compMass ends m V₁ V₂ u A = gh5_complMass ends m V₁ V₂ u A := by
-- proof
  apply StatMech.Walls.gh5_compMass_eq_complMass ends m V₁ V₂ u A hAm

/--
[gh5_complMass_eq_decoupled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_complMass_eq_decoupled_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {A : Finset ι} :
-- imply
  gh5_complMass ends m V₁ V₂ u A = gh5_complMassDecoupled ends m V₁ V₂ u A := by
-- proof
  apply StatMech.Walls.gh5_complMass_eq_decoupled ends m V₁ V₂ u A

/--
[gh5_fact2_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_fact2_factorization_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {A : Finset ι}
-- given
  (hAm : A ⊆ m) :
-- imply
  gh4_compMass ends m V₁ V₂ u A = gh5_complMassDecoupled ends m V₁ V₂ u A := by
-- proof
  apply StatMech.Walls.gh5_fact2_factorization ends m V₁ V₂ u A hAm

/--
[gh5_fact1_ghost_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_fact1_ghost_collapse_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gh3_eq22_decomposition G β h o x y = (∃ surv dropA dropB : ℝ, eg_ursell3 G β h o x y = surv - 2 * dropA - 2 * dropB ∧ 0 ≤ dropA ∧ 0 ≤ dropB) := by
-- proof
  apply StatMech.Walls.gh5_fact1_ghost_collapse G β h o x y

/--
[gh5_drop_sum_factored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_drop_sum_factored_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {wgt diff : Finset ι → ℝ} :
-- imply
  (∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgt A * diff A) = ∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgt A * diff A := by
-- proof
  apply StatMech.Walls.gh5_drop_sum_factored ends m V₁ V₂ u wgt diff

/--
[gh5_eq22_from_factored_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_eq22_from_factored_identity_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
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
  apply StatMech.Walls.gh5_eq22_from_factored_identity G β h o x y ends m V₁ V₂ V₁' V₂' u u' wgtA diffA wgtB diffB hwgtA hdiffA hwgtB hdiffB surv hident

/--
[gh5_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean)
-/
@[path]
private lemma gh5_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh5_status


-- created on 2026-10-23
