import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gh2weighted
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh2_weight_uniform_per_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_weight_uniform_per_superposition_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_threeGap G β h o x y m = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gh2_weight_uniform_per_superposition G β h o x y hox hoy hxy m hm

/--
[gh2_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_weight_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gh2_weight_nonneg G β h hβ hh m

/--
[gh2_weighted_sign_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_weighted_sign_of_count_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcount : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none ≤ 0) :
-- imply
  gc15_threeGap G β h o x y m ≤ 0 := by
-- proof
  apply StatMech.Walls.gh2_weighted_sign_of_count G β h hβ hh o x y hox hoy hxy m hcount

/--
[gh2_eq21_weighted_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_eq21_weighted_sign_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  (gc15_threeGap G β h o x y m = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m)) ∧ (#((({some x, some y, none} : Finset (Option V))).filter (fun w => connK (endsM (withGhost G) m) univ (some o) w)) = 1 ∨ #((({some x, some y, none} : Finset (Option V))).filter (fun w => connK (endsM (withGhost G) m) univ (some o) w)) = 3) := by
-- proof
  apply StatMech.Walls.gh2_eq21_weighted_sign G β h o x y hox hoy hxy m hm

/--
[gh2_lemma2_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_lemma2_weighted_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {u v : W}
  {P : Finset ι}
-- given
  (huv : u ≠ v)
  (hPm : P ⊆ m)
  (hPsrc : sources ends P = {u, v}) :
-- imply
  #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v})) = #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) := by
-- proof
  apply StatMech.Walls.gh2_lemma2_weighted G ends m A B huv P hPm hPsrc

/--
[gh2_lemma1_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_lemma1_weighted_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {G' : SimpleGraph V}
  [DecidableRel G'.Adj]
  {i j k : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β) :
-- imply
  StatMech.Ising.cov2 G' β h i j * StatMech.Ising.cov2 G' β h j k ≤ StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G' β h) (fun s => StatMech.Ising.spin s j) * StatMech.Ising.cov2 G' β h i k := by
-- proof
  apply StatMech.Walls.gh2_lemma1_weighted G G' β h hβ i j k

/--
[gh2_gks_ingredient_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_gks_ingredient_available_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  StatMech.Ising.isingExpectation G β h (StatMech.Ising.spinProd A) * StatMech.Ising.isingExpectation G β h (StatMech.Ising.spinProd B) ≤ StatMech.Ising.isingExpectation G β h (StatMech.Ising.spinProd (A ∆ B)) := by
-- proof
  apply StatMech.Walls.gh2_gks_ingredient_available G β h hβ hh A B

/--
[gh2_bridge_count_to_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_bridge_count_to_weighted_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none) :
-- imply
  gc15_threeGap G β h o x y m ≤ 0 := by
-- proof
  apply StatMech.Walls.gh2_bridge_count_to_weighted G β h hβ hh o x y hox hoy hxy m hres

/--
[gh2_graham_cor3_via_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_graham_cor3_via_count_eq
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
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh2_graham_cor3_via_count G β h hβ hh o x y hox hoy hxy hres hsupp

/--
[gh2_route_A_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_route_A_verdict_eq
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
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc15_threeGap G β h o x y m = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m)) ∧ (∀ m : ↥(withGhost G).edgeFinset → ℕ, 0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m)) ∧ ((∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none) → gc82_ThreeGapAllConnSupported G β h o x y → eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.gh2_route_A_verdict G β h hβ hh o x y hox hoy hxy

/--
[gh2_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh2weighted.lean)
-/
@[path]
private lemma gh2_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh2_status G


-- created on 2026-10-23
