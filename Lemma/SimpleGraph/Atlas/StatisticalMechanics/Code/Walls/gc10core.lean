import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10core
open Finset SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc10_core_ursell_nonpos_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_ursell_nonpos_distinct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hres : gc10_GhostFourPointSign G β h o)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc10_core_ursell_nonpos_distinct G β h o hres hox hoy hxy

/--
[gc10_core_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hres : gc10_GhostFourPointSign G β h o) :
-- imply
  GHSSignDominance G β h o := by
-- proof
  apply StatMech.Walls.gc10_core_signDominance G β h o hres

/--
[gc10_core_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : gc10_GhostFourPointSign G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc10_core_ghs G β h hβ hh o hres

/--
[gc10_core_ursell_nonpos_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_ursell_nonpos_all_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : gc10_GhostFourPointSign G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc10_core_ursell_nonpos_all G β h hβ hh o hres x y

/--
[gc10_core_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_sharpness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : gc10_GhostFourPointSign G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc10_core_sharpness G β h hβ hh o J hres hfactor

/--
[gc10_residue_of_familyRealise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_residue_of_familyRealise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hfr : gc5_FamilyRealise G β h o) :
-- imply
  gc10_GhostFourPointSign G β h o := by
-- proof
  apply StatMech.Walls.gc10_residue_of_familyRealise G β h o hfr

/--
[gc10_residue_of_eqSwi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_residue_of_eqSwi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  gc10_GhostFourPointSign G β h o := by
-- proof
  apply StatMech.Walls.gc10_residue_of_eqSwi G β h o hid

/--
[gc10_residue_concreteProb_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_residue_concreteProb_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  gc10_allConnProb ends o x y g F ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.gc10_residue_concreteProb_mem_Icc G ends o x y g F hF

/--
[gc10_residue_of_concrete_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_residue_of_concrete_identity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {g : V}
  {μ : ℝ}
  {F : Finset ι → ℝ}
-- given
  (β h : ℝ)
  (hμ : 0 ≤ μ)
  (hF : ∀ m, 0 ≤ F m)
  (hid : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → eg_ursell4_ghostPlus G β h o x y = -2 * μ * gc10_allConnProb ends o x y g F)
  (htriple : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → onePt G β h o * onePt G β h x * onePt G β h y ≤ μ * gc10_allConnProb ends o x y g F) :
-- imply
  gc10_GhostFourPointSign G β h o := by
-- proof
  apply StatMech.Walls.gc10_residue_of_concrete_identity G β h o ends g μ F hμ hF hid htriple

/--
[gc10_core_ghs_of_concrete_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_ghs_of_concrete_identity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {g : V}
  {μ : ℝ}
  {F : Finset ι → ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hμ : 0 ≤ μ)
  (hF : ∀ m, 0 ≤ F m)
  (hid : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → eg_ursell4_ghostPlus G β h o x y = -2 * μ * gc10_allConnProb ends o x y g F)
  (htriple : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → onePt G β h o * onePt G β h x * onePt G β h y ≤ μ * gc10_allConnProb ends o x y g F) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc10_core_ghs_of_concrete_identity G β h hβ hh o ends g μ F hμ hF hid htriple

/--
[gc10_core_ghs_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_ghs_degenerate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  eg_ursell4_ghost G β h x x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc10_core_ghs_degenerate G β h hβ hh x y hxy

/--
[gc10_core_ursell_nonpos_xeqy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_core_ursell_nonpos_xeqy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x) :
-- imply
  eg_ursell3 G β h o x x ≤ 0 := by
-- proof
  apply StatMech.Walls.gc10_core_ursell_nonpos_xeqy G β h hβ hh o x hox

/--
[gc10_residue_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10core.lean)
-/
@[path]
private lemma gc10_residue_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  eg_ursell3 (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 = eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 + 2 * (onePt (⊤ : SimpleGraph (Fin 3)) 1 1 0 * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 1 * onePt (⊤ : SimpleGraph (Fin 3)) 1 1 2) := by
-- proof
  apply StatMech.Walls.gc10_residue_nonvacuous G


-- created on 2026-10-23
