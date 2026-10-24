import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc25resummation
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc25_nativeAllConnMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_nativeAllConnMass_nonneg_eq
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
  0 ≤ gc25_nativeAllConnMass G β h o x y := by
-- proof
  apply StatMech.Walls.gc25_nativeAllConnMass_nonneg G β h hβ hh o x y

/--
[gc25_ursell_nonpos_of_nativeResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_ursell_nonpos_of_nativeResummation_eq
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
  (hres : gc25_NativeResummation G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc25_ursell_nonpos_of_nativeResummation G β h hβ hh o x y hox hoy hxy hres

/--
[gc25_ghs_of_nativeResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_ghs_of_nativeResummation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc25_ghs_of_nativeResummation G β h hβ hh o hres

/--
[gc25_aizenman_barsky_of_nativeResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_aizenman_barsky_of_nativeResummation_eq
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
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc25_aizenman_barsky_of_nativeResummation G β h hβ hh o J hres hfactor

/--
[gc25_leadingGap_eq_disconnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_leadingGap_eq_disconnSum_eq
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
  currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none} : Finset (Option V)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y} = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none} : Finset (Option V)) ∅ (some x) (some y) := by
-- proof
  apply StatMech.Walls.gc25_leadingGap_eq_disconnSum G β h o x y hox hoy hxy

/--
[gc25_nativeAllConnMass_eq_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_nativeAllConnMass_eq_gap_eq
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
  gc25_nativeAllConnMass G β h o x y = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none} : Finset (Option V)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y} := by
-- proof
  apply StatMech.Walls.gc25_nativeAllConnMass_eq_gap G β h o x y hox hoy hxy

/--
[gc25_threeGap_sum_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_threeGap_sum_decomp_eq
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
  (∑' m, gc15_threeGap G β h o x y m) = gc15_Z0 G β h * gc25_nativeAllConnMass G β h o x y - gc15_Z0 G β h * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none} - gc15_Z0 G β h * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none} + 2 * (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}) := by
-- proof
  apply StatMech.Walls.gc25_threeGap_sum_decomp G β h o x y hox hoy hxy

/--
[gc25_three_switchingGaps_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_three_switchingGaps_nonneg_eq
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
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
-- proof
  apply StatMech.Walls.gc25_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy

/--
[gc25_witness_structure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_witness_structure_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  (∀ m : Finset (Fin 2), (0 : ℝ) ≤ (fun _ => (1 : ℝ)) m) ∧ (∀ i, ¬ (witEnds i).IsDiag) ∧ (¬ connK witEnds witM (0 : Fin 4) 3 ∧ sources witEnds witM = {0, 1, 2, 3}) := by
-- proof
  apply StatMech.Walls.gc25_witness_structure G

/--
[gc25_nativeAllConnMass_eq_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_nativeAllConnMass_eq_edgecopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gc25_nativeAllConnMass G β h o x y = ∑' m : ↥(withGhost G).edgeFinset → ℕ, (∑ S : Finset (Copy (withGhost G) m), (if RandomCurrent.sources (endsM (withGhost G) m) S = (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM (withGhost G) m) (univ \ S) = ∅ then 1 else 0) * (if ¬ RandomCurrent.connK (endsM (withGhost G) m) univ (some o) none then 1 else 0)) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gc25_nativeAllConnMass_eq_edgecopy G β h o x y

/--
[gc25_backbone_not_signDefinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_backbone_not_signDefinite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 (Option V)}
  {m₁ m₂ : Finset ι}
  {o x y : V}
-- given
  (h₁ : connK ends m₁ (some x) (some y) ∧ connK ends m₁ (some o) (some y) ∧ connK ends m₁ (some o) (some x))
  (h₂ : ¬ connK ends m₂ (some x) (some y) ∧ ¬ connK ends m₂ (some o) (some y) ∧ ¬ connK ends m₂ (some o) (some x)) :
-- imply
  asd_ghsBackboneFactor ends m₁ (some o) (some x) (some y) < 0 ∧ 0 < asd_ghsBackboneFactor ends m₂ (some o) (some x) (some y) := by
-- proof
  apply StatMech.Walls.gc25_backbone_not_signDefinite G ends m₁ m₂ h₁ h₂

/--
[gc25_native_and_edgecopy_both_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc25resummation.lean)
-/
@[path]
private lemma gc25_native_and_edgecopy_both_close_eq
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
  (gc25_NativeResummation G β h o x y → eg_ursell3 G β h o x y ≤ 0) ∧ (gc24_ThreeReplicaResummation G β h o x y → eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.gc25_native_and_edgecopy_both_close G β h hβ hh o x y hox hoy hxy


-- created on 2026-10-23
