import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc5_core
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc5_core_ensemble_ursell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_ensemble_ursell_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  egh_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y := by
-- proof
  apply StatMech.Walls.gc5_core_ensemble_ursell_eq G β J M B hox hoy hxy

/--
[gc5_core_ensemble_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_ensemble_prob_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Ising.Current V)}
  {B : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.gc5_core_ensemble_prob_le_one G β J hβ hJ M B o x y

/--
[gc5_core_bracket_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_bracket_sign_eq
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
  -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_core_bracket_sign G β J hβ hJ M B o x y hμ

/--
[gc5_core_u3_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_u3_nonpos_eq
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
  apply StatMech.Walls.gc5_core_u3_nonpos G β J hβ hJ M B o x y hμ

/--
[gc5_core_ursell_eq_lebowitz_plus_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_ursell_eq_lebowitz_plus_triple_eq
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
  apply StatMech.Walls.gc5_core_ursell_eq_lebowitz_plus_triple G β h o x y

/--
[gc5_core_lebowitz_le_ursell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_lebowitz_le_ursell_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  gc_lebowitzU4 G β h o x y ≤ eg_ursell3 G β h o x y := by
-- proof
  apply StatMech.Walls.gc5_core_lebowitz_le_ursell G β h hβ hh o x y

/--
[gc5_core_ursell_nonpos_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_ursell_nonpos_of_signDominance_eq
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
  (hsd : GHSSignDominance G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_core_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y

/--
[gc5_core_ghs_concavity_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_ghs_concavity_of_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc5_core_ghs_concavity_of_signDominance G β h hβ hh o hsd

/--
[gc5_core_aizenman_barsky_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_aizenman_barsky_of_signDominance_eq
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
  (hsd : GHSSignDominance G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc5_core_aizenman_barsky_of_signDominance G β h hβ hh o J hsd hfactor

/--
[gc5_core_signDominance_of_familyRealise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_signDominance_of_familyRealise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hfr : gc5_FamilyRealise G β h o) :
-- imply
  GHSSignDominance G β h o := by
-- proof
  apply StatMech.Walls.gc5_core_signDominance_of_familyRealise G β h o hfr

/--
[gc5_core_ursell_nonpos_of_familyRealise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_ursell_nonpos_of_familyRealise_eq
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
  (hfr : gc5_FamilyRealise G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc5_core_ursell_nonpos_of_familyRealise G β h hβ hh o hfr x y

/--
[gc5_core_ghs_concavity_of_familyRealise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_ghs_concavity_of_familyRealise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hfr : gc5_FamilyRealise G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc5_core_ghs_concavity_of_familyRealise G β h hβ hh o hfr

/--
[gc5_core_sharpness_of_familyRealise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_sharpness_of_familyRealise_eq
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
  (hfr : gc5_FamilyRealise G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc5_core_sharpness_of_familyRealise G β h hβ hh o J hfr hfactor

/--
[gc5_familyRealise_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_familyRealise_degenerate_eq
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
  apply StatMech.Walls.gc5_familyRealise_degenerate G β h hβ hh x y hxy

/--
[gc5_familyRealise_bracket_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_familyRealise_bracket_surjective_eq
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
  apply StatMech.Walls.gc5_familyRealise_bracket_surjective G hμ hlo hhi

/--
[gc5_core_bracket_free_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_bracket_free_endpoints_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ℝ} :
-- imply
  (-2 * μ * (1 : ℝ) = -2 * μ) ∧ (-2 * μ * (0 : ℝ) = 0) := by
-- proof
  apply StatMech.Walls.gc5_core_bracket_free_endpoints G μ

/--
[gc5_core_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean)
-/
@[path]
private lemma gc5_core_consistent_eq
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
  (-2 * μ * tcp_allConnProb G β J M B o x y ≤ 0) ∧ tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.gc5_core_consistent G β J hβ hJ M B o x y hμ


-- created on 2026-10-23
