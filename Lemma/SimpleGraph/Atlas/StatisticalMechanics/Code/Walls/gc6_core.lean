import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc6_core
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc6_core_mu_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_mu_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Walls.gc6_core_mu_nonneg G β h hβ hh A

/--
[gc6_core_familyRealise_of_eqSwi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_familyRealise_of_eqSwi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  gc5_FamilyRealise G β h o := by
-- proof
  apply StatMech.Walls.gc6_core_familyRealise_of_eqSwi G β h o hid

/--
[gc6_core_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  GHSSignDominance G β h o := by
-- proof
  apply StatMech.Walls.gc6_core_signDominance G β h o hid

/--
[gc6_core_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_ursell_nonpos_eq
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
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc6_core_ursell_nonpos G β h hβ hh o hid x y

/--
[gc6_core_ghs_concavity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_ghs_concavity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc6_core_ghs_concavity G β h hβ hh o hid

/--
[gc6_core_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_sharpness_eq
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
  (hid : gc6_EqSwiIdentity G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc6_core_sharpness G β h hβ hh o J hid hfactor

/--
[gc6_core_bracket_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_bracket_surjective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ t : ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hlo : -2 * μ ≤ t)
  (hhi : t ≤ 0) :
-- imply
  ∃ P : ℝ, 0 ≤ P ∧ P ≤ 1 ∧ -2 * μ * P = t := by
-- proof
  apply StatMech.Walls.gc6_core_bracket_surjective G hμ hlo hhi

/--
[gc6_core_sharpening](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_sharpening_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  gc5_FamilyRealise G β h o := by
-- proof
  apply StatMech.Walls.gc6_core_sharpening G β h o hid

/--
[gc6_core_eqSwi_degenerate_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_eqSwi_degenerate_shape_eq
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
  ∃ μ : ℝ, 0 ≤ μ ∧ eg_ursell3 G β h x x y = -2 * μ * 1 := by
-- proof
  apply StatMech.Walls.gc6_core_eqSwi_degenerate_shape G β h hβ hh x y hxy

/--
[gc6_core_mu_clause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_mu_clause_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  ∃ μ : ℝ, 0 ≤ μ ∧ μ = isingExpectation G β h (spinProd A) := by
-- proof
  apply StatMech.Walls.gc6_core_mu_clause G β h hβ hh A

/--
[gc6_core_ursell_eq_lebowitz_plus_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_ursell_eq_lebowitz_plus_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y = gc_lebowitzU4 G β h o x y + 2 * isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y) := by
-- proof
  apply StatMech.Walls.gc6_core_ursell_eq_lebowitz_plus_triple G β h o x y

/--
[gc6_core_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean)
-/
@[path]
private lemma gc6_core_consistent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
  {μ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hμ : 0 ≤ μ) :
-- imply
  -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc6_core_consistent G β J hβ hJ M B o x y hμ


-- created on 2026-10-23
