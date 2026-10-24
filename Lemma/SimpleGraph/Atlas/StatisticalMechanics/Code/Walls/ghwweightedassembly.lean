import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.ghwweightedassembly
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[ghw_step1_resum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_step1_resum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = ∑' m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m := by
-- proof
  apply StatMech.Walls.ghw_step1_resum G β h o x y hox hoy hxy

/--
[ghw_step2_regroup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_step2_regroup_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W} :
-- imply
  (gc85b_pcount ends m V₁ V₂ : ℝ) = ∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) := by
-- proof
  apply StatMech.Walls.ghw_step2_regroup ends m V₁ V₂ u

/--
[ghw_step3_gks_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_step3_gks_drop_eq
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
  apply StatMech.Walls.ghw_step3_gks_drop G β h o x y ends m u u' heq22

/--
[ghw_step4_lemma1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_step4_lemma1_eq
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
  apply StatMech.Walls.ghw_step4_lemma1 G β h hβ i j k

/--
[ghw_chain_step3_step4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_chain_step3_step4_eq
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
  (heq22 : ∃ (V₁ V₂ V₁' V₂' : Finset W) (wgtA diffA wgtB diffB : Finset ι → ℝ), (∀ A, 0 ≤ wgtA A) ∧ (∀ A, 0 ≤ diffA A) ∧ (∀ B, 0 ≤ wgtB B) ∧ (∀ B, 0 ≤ diffB B) ∧ eg_ursell3 G β h o x y = surv - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A) - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B))
  (hsurv : surv ≤ 0) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghw_chain_step3_step4 G β h o x y ends m u u' heq22 hsurv

/--
[ghw_ghs_assembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_ghs_assembly_eq
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
  apply StatMech.Walls.ghw_ghs_assembly G β h o x y ends m u u' heq22

/--
[ghw_surv_is_free_existential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_surv_is_free_existential_eq
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
  (hghs : eg_ursell3 G β h o x y ≤ 0) :
-- imply
  gh8_weighted_eq22 G β h o x y ends m u u' := by
-- proof
  apply StatMech.Walls.ghw_surv_is_free_existential G β h o x y ends m u u' hghs

/--
[ghw_weighted_eq22_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_weighted_eq22_iff_eq
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
  (β h : ℝ) :
-- imply
  gh8_weighted_eq22 G β h o x y ends m u u' ↔ eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghw_weighted_eq22_iff G β h o x y ends m u u'

/--
[ghw_surv_not_bound_to_lemma1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_surv_not_bound_to_lemma1_eq
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
  (β h : ℝ) :
-- imply
  gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u' ↔ eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghw_surv_not_bound_to_lemma1 G β h o x y ends m u u'

/--
[ghw_ghs_nonCircular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_ghs_nonCircular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbij : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.ghw_ghs_nonCircular G β h hβ hh o x y hox hoy hxy hbij hsupp

/--
[ghw_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghwweightedassembly.lean)
-/
@[path]
private lemma ghw_status_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.ghw_status


-- created on 2026-10-23
