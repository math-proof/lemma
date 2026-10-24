import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackbonePropsFull
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_mem_backboneSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_mem_backboneSet_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {ω : G.Path x y} :
-- imply
  ω ∈ shb_backboneSet G n x y ↔ shb_IsBackboneOf G n x y ω := by
-- proof
  apply StatMech.Sharpness.shb_mem_backboneSet G n x y ω

/--
[shb_isBackbonePath_mem_backboneSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_isBackbonePath_mem_backboneSet_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {p : IsBackbonePath G n x y} :
-- imply
  (⟨p.1.mapLe (oddSubgraph_le G n), p.2.mapLe (oddSubgraph_le G n)⟩ : G.Path x y) ∈ shb_backboneSet G n x y := by
-- proof
  apply StatMech.Sharpness.shb_isBackbonePath_mem_backboneSet G n x y p

/--
[shb_adjP_oddEdges_imp_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_adjP_oddEdges_imp_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {a b : V}
-- given
  (h : StatMech.Ising.adjP (StatMech.Ising.oddEdges G.edgeFinset n) a b) :
-- imply
  (oddSubgraph G n).Adj a b := by
-- proof
  apply StatMech.Sharpness.shb_adjP_oddEdges_imp_adj G n h

/--
[shb_connP_oddEdges_imp_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_connP_oddEdges_imp_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {a b : V}
-- given
  (h : StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset n) a b) :
-- imply
  (oddSubgraph G n).Reachable a b := by
-- proof
  apply StatMech.Sharpness.shb_connP_oddEdges_imp_reachable G n h

/--
[shb_sources_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_sources_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V} :
-- imply
  Sharpness.sources G n = StatMech.Ising.sources G.edgeFinset n := by
-- proof
  apply StatMech.Sharpness.shb_sources_eq G n

/--
[shb_backbone_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_backbone_exists_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
-- given
  (hxy : x ≠ y)
  (hsrc : Sharpness.sources G n = {x, y}) :
-- imply
  Nonempty (IsBackbonePath G n x y) := by
-- proof
  apply StatMech.Sharpness.shb_backbone_exists G n hxy hsrc

/--
[shb_backboneSet_nonempty_of_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_backboneSet_nonempty_of_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
-- given
  (hxy : x ≠ y)
  (hsrc : Sharpness.sources G n = {x, y}) :
-- imply
  (shb_backboneSet G n x y).Nonempty := by
-- proof
  apply StatMech.Sharpness.shb_backboneSet_nonempty_of_sources G n hxy hsrc

/--
[shb_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_weight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n : Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weight G β J n := by
-- proof
  apply StatMech.Sharpness.shb_weight_nonneg G β J hβ hJ n

/--
[shb_summable_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_summable_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => weight G β J (ofEdgeFun G m)) := by
-- proof
  apply StatMech.Sharpness.shb_summable_weight G β J

/--
[shb_summable_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_summable_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  [DecidablePred P]
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (P : (↥G.edgeFinset → ℕ) → Prop) :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => if P m then weight G β J (ofEdgeFun G m) else 0) := by
-- proof
  apply StatMech.Sharpness.shb_summable_indicator G β J hβ hJ P

/--
[shb_indicator_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_indicator_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hxy : x ≠ y) :
-- imply
  (if Sharpness.sources G (ofEdgeFun G m) = {x, y} then weight G β J (ofEdgeFun G m) else 0) = ∑ ω : G.Path x y, (if Sharpness.sources G (ofEdgeFun G m) = {x, y} ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some ω then weight G β J (ofEdgeFun G m) else 0) := by
-- proof
  apply StatMech.Sharpness.shb_indicator_eq_sum G β J hxy m

/--
[shb_currentSum_eq_sum_backboneNum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_currentSum_eq_sum_backboneNum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hxy : x ≠ y) :
-- imply
  currentSum G β J {x, y} = ∑ ω : G.Path x y, shb_backboneNum G β J x y ω := by
-- proof
  apply StatMech.Sharpness.shb_currentSum_eq_sum_backboneNum G β J hβ hJ hxy

/--
[shb_P1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_P1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hxy : x ≠ y) :
-- imply
  expectationJ G β J {x, y} = ∑ ω : G.Path x y, shb_rho G β J x y ω := by
-- proof
  apply StatMech.Sharpness.shb_P1 G β J hβ hJ hxy

/--
[shb_P1_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean)
-/
@[path]
private lemma shb_P1_ising_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {x y : V}
-- given
  (hβ : 0 ≤ β)
  (hxy : x ≠ y) :
-- imply
  StatMech.Ising.isingExpectation G β 0 (StatMech.Ising.spinProd {x, y}) = ∑ ω : G.Path x y, shb_rho G β (fun _ => 1) x y ω := by
-- proof
  apply StatMech.Sharpness.shb_P1_ising G β hβ hxy


-- created on 2026-10-23
