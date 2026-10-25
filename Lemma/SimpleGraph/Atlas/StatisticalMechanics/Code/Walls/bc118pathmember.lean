import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc118pathmember
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc118_interiorPendant_not_covered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_interiorPendant_not_covered_eq
  {F : SimpleGraph V}
  {B H : V → Prop}
  {v : V}
-- given
  (hnotint : ¬ bc114_IsInternal F v)
  (hvB : ¬ B v)
  (hvH : ¬ H v) :
-- imply
  ¬ bc116_ThroughPathCovered F B H := by
-- proof
  apply StatMech.Walls.bc118_interiorPendant_not_covered F hnotint hvB hvH

/--
[bc118_degreeOnePendant_not_covered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_degreeOnePendant_not_covered_eq
  [Fintype V]
  [DecidableEq V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {B H : V → Prop}
  {v : V}
-- given
  (hdeg : F.degree v = 1)
  (hvB : ¬ B v)
  (hvH : ¬ H v) :
-- imply
  ¬ bc116_ThroughPathCovered F B H := by
-- proof
  apply StatMech.Walls.bc118_degreeOnePendant_not_covered F hdeg hvB hvH

/--
[bc118_concrete_interiorPendant_not_covered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_concrete_interiorPendant_not_covered_eq :
-- imply
  ¬ bc116_ThroughPathCovered (SimpleGraph.fromEdgeSet {s((0 : Fin 2), 1)}) (fun w => w = 0) (fun _ => False) := by
-- proof
  apply StatMech.Walls.bc118_concrete_interiorPendant_not_covered

/--
[bc118_pathUnion_can_have_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_pathUnion_can_have_pendant_eq :
-- imply
  ∃ (F' : SimpleGraph (Fin 3)) (_ : DecidableRel F'.Adj) (v : Fin 3), F'.degree v = 1 ∧ ¬ bc114_IsInternal F' v := by
-- proof
  apply StatMech.Walls.bc118_pathUnion_can_have_pendant

/--
[bc118_count_unconditional_leaf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_count_unconditional_leaf_bound_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc118_count_unconditional_leaf_bound G hacyc hmin

/--
[bc118_count_closes_via_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_count_closes_via_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc118_count_closes_via_forest ω L R h

/--
[bc118_membership_NOT_needed_for_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_membership_NOT_needed_for_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) := by
-- proof
  apply StatMech.Walls.bc118_membership_NOT_needed_for_count ω L R

/--
[bc118_membership_suffices_but_is_not_the_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_membership_suffices_but_is_not_the_route_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {B H : V → Prop}
-- given
  (hcov : bc116_ThroughPathCovered F B H)
  (hhub : ∀ v, H v → 3 ≤ F.degree v)
  (hac : F.IsAcyclic)
  (hmin : ∀ v, 1 ≤ F.degree v) :
-- imply
  F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) := by
-- proof
  apply StatMech.Walls.bc118_membership_suffices_but_is_not_the_route F hcov hhub hac hmin

/--
[bc118_count_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_count_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc118_count_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bc118_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc118pathmember.lean)
-/
@[path]
private lemma bc118_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj] (B H : V → Prop) (v : V), F.degree v = 1 → ¬ B v → ¬ H v → ¬ bc116_ThroughPathCovered F B H) ∧ (∃ (F' : SimpleGraph (Fin 3)) (_ : DecidableRel F'.Adj) (v : Fin 3), F'.degree v = 1 ∧ ¬ bc114_IsInternal F' v) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) := by
-- proof
  apply StatMech.Walls.bc118_status


-- created on 2026-10-23
