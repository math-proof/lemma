import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfkforestcount
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfk_forestHandshake](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_forestHandshake_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bfk_forestHandshake G hacyc hmin

/--
[bfk_forestCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_forestCount_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype ι]
  {f : ι → V}
  {B : Finset V}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hf : Function.Injective f)
  (hdeg3 : ∀ i, 3 ≤ G.degree (f i))
  (hleaf : ∀ v, G.degree v = 1 → v ∈ B) :
-- imply
  Fintype.card ι ≤ B.card := by
-- proof
  apply StatMech.Walls.bfk_forestCount G hacyc hmin f hf hdeg3 B hleaf

/--
[bfk_armForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_armForest_acyclic_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {Gs : ι → SimpleGraph V}
-- given
  (hT : T.IsTree)
  (hle : ∀ i, Gs i ≤ T) :
-- imply
  (⨆ i, Gs i).IsAcyclic := by
-- proof
  apply StatMech.Walls.bfk_armForest_acyclic hT Gs hle

/--
[bfk_armRay_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_armRay_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w x : Site d}
  {R : ℕ}
-- given
  (hT : T ≤ openSubgraph d ω)
  (hR : 1 ≤ R)
  (hwx : w ≠ x)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bfk_armRay_reaches_boundary T hT hR hwx hw hinf

/--
[bfk_star_count_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_star_count_witness_eq
  {d : ℕ} :
-- imply
  Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := by
-- proof
  apply StatMech.Walls.bfk_star_count_witness

/--
[bfk_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_datum_implies_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (h : bau_ArmSubforestData ω 0 R) :
-- imply
  bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bfk_datum_implies_count ω R h

/--
[bfk_bk_of_datum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_bk_of_datum_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bfk_bk_of_datum p hp1 hp0 hdata

/--
[bfk_forestCount_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfkforestcount.lean)
-/
@[path]
private lemma bfk_forestCount_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] [Nonempty V] {G : SimpleGraph V} [_i : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] {G : SimpleGraph V} [_i : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → ∀ {ι : Type} [Fintype ι] (f : ι → V), Function.Injective f → (∀ i, 3 ≤ G.degree (f i)) → ∀ (B : Finset V), (∀ v, G.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧ (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V), (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧ (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bau_ArmSubforestData ω 0 R → bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R) ∧ (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bfk_forestCount_status


-- created on 2026-10-23
