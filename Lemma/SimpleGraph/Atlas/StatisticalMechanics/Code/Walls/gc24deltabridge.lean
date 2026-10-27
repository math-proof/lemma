import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc24_splitWeightedSum_eq_fibreCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_splitWeightedSum_eq_fibreCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {p : ↥G.edgeFinset → ℕ}
  {A : Finset V} :
-- imply
  splitWeightedSum G β J (ofEdgeFun G p) 1 A = (gc24_fibreCount G p A : ℝ) * weight G β J (ofEdgeFun G p) := by
-- proof
  apply StatMech.Walls.gc24_splitWeightedSum_eq_fibreCount G β J p A

/--
[gc24_tpsum_eq_fibreCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_tpsum_eq_fibreCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  gc15_tpsum G β J m A B = ∑ K₂ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e}, (if sources G (ofEdgeFun G K₂.1) = B then weight G β J (ofEdgeFun G K₂.1) else 0) * ((gc24_fibreCount G (fun e => m e - K₂.1 e) A : ℝ) * weight G β J (ofEdgeFun G (fun e => m e - K₂.1 e))) := by
-- proof
  apply StatMech.Walls.gc24_tpsum_eq_fibreCount G β J m A B

/--
[gc24_fibreCount_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_fibreCount_backbone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ↥G.edgeFinset → ℕ}
  {A : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : RandomCurrent.sources (endsM G p) (univ : Finset (Copy G p)) = A) :
-- imply
  ((gc24_fibreCount G p A : ℝ) - (gc24_fibreCount G p (A ∆ {x, y}) : ℝ) - (gc24_fibreCount G p (A ∆ {o, y}) : ℝ) - (gc24_fibreCount G p (A ∆ {o, x}) : ℝ)) = (gc24_fibreCount G p A : ℝ) * (1 - (if connK (endsM G p) (univ : Finset (Copy G p)) x y then 1 else 0) - (if connK (endsM G p) (univ : Finset (Copy G p)) o y then 1 else 0) - (if connK (endsM G p) (univ : Finset (Copy G p)) o x then 1 else 0)) := by
-- proof
  apply StatMech.Walls.gc24_fibreCount_backbone G p A hox hoy hxy hm

/--
[gc24_sourcePairDisconnSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_sourcePairDisconnSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ sourcePairDisconnSum G β J A B u v := by
-- proof
  apply StatMech.Walls.gc24_sourcePairDisconnSum_nonneg G β J hβ hJ A B u v

/--
[gc24_switchingGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_switchingGap_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (huv : u ≠ v) :
-- imply
  currentSum G β J (A ∆ {u, v}) * currentSum G β J {u, v} ≤ currentSum G β J A * currentSum G β J ∅ := by
-- proof
  apply StatMech.Walls.gc24_switchingGap_nonneg G β J hβ hJ A huv

/--
[gc24_three_switchingGaps_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_three_switchingGaps_nonneg_eq
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
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, none} : Finset (Option V)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
-- proof
  apply StatMech.Walls.gc24_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy

/--
[gc24_ursell_nonpos_of_threeReplicaResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_ursell_nonpos_of_threeReplicaResummation_eq
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
  (hres : gc24_ThreeReplicaResummation G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc24_ursell_nonpos_of_threeReplicaResummation G β h o x y hox hoy hxy hres

/--
[gc24_ghs_of_threeReplicaResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_ghs_of_threeReplicaResummation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc24_ThreeReplicaResummation G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc24_ghs_of_threeReplicaResummation G β h hβ hh o hres

/--
[gc24_aizenman_barsky_of_threeReplicaResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_aizenman_barsky_of_threeReplicaResummation_eq
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
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc24_ThreeReplicaResummation G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc24_aizenman_barsky_of_threeReplicaResummation G β h hβ hh o J hres hfactor

/--
[gc24_backbone_not_signDefinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_backbone_not_signDefinite_eq
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
  apply StatMech.Walls.gc24_backbone_not_signDefinite G ends m₁ m₂ h₁ h₂

/--
[gc24_allConnMass_eq_caseA_plus_caseB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean)
-/
@[path]
private lemma gc24_allConnMass_eq_caseA_plus_caseB_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 (Option V)}
  {F : Finset ι → ℝ}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m (some o) none) → sources ends m = {some o, some x, some y, none}) :
-- imply
  gc10_allConnMass ends (some o) (some x) (some y) none F = drd_pairSum ends ({some o, some x, some y, none} : Finset (Option V)) F (fun m => gc8_caseA ends (some o) (some x) (some y) none m) + drd_pairSum ends ({some o, some x, some y, none} : Finset (Option V)) F (fun m => gc8_caseB ends (some o) (some x) (some y) none m) := by
-- proof
  apply StatMech.Walls.gc24_allConnMass_eq_caseA_plus_caseB G ends F hox hoy hxy hnd hsrcSet


-- created on 2026-10-23
