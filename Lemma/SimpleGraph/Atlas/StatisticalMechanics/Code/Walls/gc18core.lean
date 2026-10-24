import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc18core
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc18_star_gap_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_star_gap_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m' : Ising.Current V}
  {o x y g : V}
  {Hog : connP (oddEdges G.edgeFinset m') o g}
  {Hox : connP (oddEdges G.edgeFinset m') o x}
  {Hoy : connP (oddEdges G.edgeFinset m') o y}
-- given
  (hog : o ≠ g)
  (hox : o ≠ x)
  (hoy : o ≠ y) :
-- imply
  hnw_mass G β J m' ∅ - hnw_mass G β J m' {o, g} - hnw_mass G β J m' {o, x} - hnw_mass G β J m' {o, y} = -2 * hnw_mass G β J m' ∅ := by
-- proof
  apply StatMech.Walls.gc18_star_gap_allConn G β J m' hog hox hoy Hog Hox Hoy

/--
[gc18_star_gap_allConn_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_star_gap_allConn_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m' : Ising.Current V}
  {o x y g : V}
  {Hog : connP (oddEdges G.edgeFinset m') o g}
  {Hox : connP (oddEdges G.edgeFinset m') o x}
  {Hoy : connP (oddEdges G.edgeFinset m') o y}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hog : o ≠ g)
  (hox : o ≠ x)
  (hoy : o ≠ y) :
-- imply
  hnw_mass G β J m' ∅ - hnw_mass G β J m' {o, g} - hnw_mass G β J m' {o, x} - hnw_mass G β J m' {o, y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc18_star_gap_allConn_nonpos G β J hβ hJ m' hog hox hoy Hog Hox Hoy

/--
[gc18_star_mass_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_star_mass_vanish_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m' : Ising.Current V}
  {u v : V}
-- given
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (huv : u ≠ v)
  (hdisc : ¬ connP (posEdges G.edgeFinset m') u v) :
-- imply
  hnw_mass G β J m' {u, v} = 0 := by
-- proof
  apply StatMech.Walls.gc18_star_mass_vanish G β J m' hnd huv hdisc

/--
[gc18_pair_mass_le_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_pair_mass_le_base_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m' : Ising.Current V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (huv : u ≠ v)
  (hreg : connP (oddEdges G.edgeFinset m') u v ∨ ¬ connP (posEdges G.edgeFinset m') u v) :
-- imply
  hnw_mass G β J m' {u, v} ≤ hnw_mass G β J m' ∅ := by
-- proof
  apply StatMech.Walls.gc18_pair_mass_le_base G β J hβ hJ m' hnd huv hreg

/--
[gc18_starGap_le_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_starGap_le_base_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m' : Ising.Current V}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hog : o ≠ g)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hg : connP (oddEdges G.edgeFinset m') o g ∨ ¬ connP (posEdges G.edgeFinset m') o g)
  (hx : connP (oddEdges G.edgeFinset m') o x ∨ ¬ connP (posEdges G.edgeFinset m') o x)
  (hy : connP (oddEdges G.edgeFinset m') o y ∨ ¬ connP (posEdges G.edgeFinset m') o y) :
-- imply
  hnw_mass G β J m' ∅ - hnw_mass G β J m' {o, g} - hnw_mass G β J m' {o, x} - hnw_mass G β J m' {o, y} ≤ hnw_mass G β J m' ∅ := by
-- proof
  apply StatMech.Walls.gc18_starGap_le_base G β J hβ hJ m' hnd hog hox hoy hg hx hy

/--
[gc18_firstFour_reorg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_firstFour_reorg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1) else 0) * (hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅ - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none} - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x} - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y}) := by
-- proof
  apply StatMech.Walls.gc18_firstFour_reorg G β h o x y m

/--
[gc18_fifth_reorg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_fifth_reorg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none} then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1) else 0) * hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none} := by
-- proof
  apply StatMech.Walls.gc18_fifth_reorg G β h o x y m

/--
[gc18_weightedPathCrossing_iff_cert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_weightedPathCrossing_iff_cert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gc18_WeightedPathCrossing G β h o x y ↔ gc16_PerConfigCert G β h o x y := by
-- proof
  apply StatMech.Walls.gc18_weightedPathCrossing_iff_cert G β h o x y

/--
[gc18_firstFour_nonpos_of_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_firstFour_nonpos_of_allConn_eq
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
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (hall : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none ∧ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x) ∧ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc18_firstFour_nonpos_of_allConn G β h hβ hh o x y hog hoxs hoys m hall

/--
[gc18_fifth_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_fifth_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} := by
-- proof
  apply StatMech.Walls.gc18_fifth_nonneg G β h hβ hh o x m

/--
[gc18_ursell_nonpos_of_weightedPathCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_ursell_nonpos_of_weightedPathCrossing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hwpc : gc18_WeightedPathCrossing G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc18_ursell_nonpos_of_weightedPathCrossing G β h o x y hox hoy hxy hwpc

/--
[gc18_ghs_of_weightedPathCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_ghs_of_weightedPathCrossing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hwpc : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc18_WeightedPathCrossing G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc18_ghs_of_weightedPathCrossing G β h hβ hh o hwpc

/--
[gc18_aizenman_barsky_of_weightedPathCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_aizenman_barsky_of_weightedPathCrossing_eq
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
  (hwpc : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc18_WeightedPathCrossing G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc18_aizenman_barsky_of_weightedPathCrossing G β h hβ hh o J hwpc hfactor

/--
[gc18_combinatorial_forcing_supplies_starCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_combinatorial_forcing_supplies_starCollapse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V}
-- given
  (hox : RandomCurrent.connK ends K o x)
  (hoy : RandomCurrent.connK ends K o y)
  (hog : RandomCurrent.connK ends K o g) :
-- imply
  RandomCurrent.connK ends K o o ∧ RandomCurrent.connK ends K o x ∧ RandomCurrent.connK ends K o y ∧ RandomCurrent.connK ends K o g := by
-- proof
  apply StatMech.Walls.gc18_combinatorial_forcing_supplies_starCollapse G ends K hox hoy hog

/--
[gc18_distinct_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean)
-/
@[path]
private lemma gc18_distinct_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hwpc : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc18_WeightedPathCrossing G β h o x y)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc18_distinct_ursell_nonpos G β h o hwpc hox hoy hxy


-- created on 2026-10-23
