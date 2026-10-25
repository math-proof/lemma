import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bof2leafcount.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bof2_forest_handshake](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_forest_handshake_eq
  [Fintype V]
  [DecidableEq V]
  {T : SimpleGraph V}
  [DecidableRel T.Adj]
-- given
  (hT : T.IsTree) :
-- imply
  (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card ≤ (Finset.univ.filter (fun v => T.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bof2_forest_handshake hT

/--
[bof2_trifCount_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_trifCount_le_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {H T : SimpleGraph V}
  [DecidableRel T.Adj]
  [Fintype ι]
  {f : ι → V}
  {B : Finset V}
-- given
  (hTH : T ≤ H)
  (hT : T.IsTree)
  (hf : Function.Injective f)
  (hcut : ∀ i, ∃ a₁ a₂ a₃ : V, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧ ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₂ ∧ ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₃ ∧ ¬ (bkg_deleteVertex H (f i)).Reachable a₂ a₃)
  (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
-- imply
  Fintype.card ι ≤ B.card := by
-- proof
  apply StatMech.Walls.bof2_trifCount_le_boundary hTH hT f hf hcut B hleaf

/--
[bof2_bgnW_handshake_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_bgnW_handshake_witness_eq :
-- imply
  (Finset.univ.filter (fun v => 3 ≤ bcv_T0.degree v)).card = 2 ∧ (Finset.univ.filter (fun v => bcv_T0.degree v = 1)).card = 6 ∧ (Finset.univ.filter (fun v => 3 ≤ bcv_T0.degree v)).card ≤ (Finset.univ.filter (fun v => bcv_T0.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bof2_bgnW_handshake_witness

/--
[bof2_bgnW_handshake_applies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_bgnW_handshake_applies_eq :
-- imply
  (Finset.univ.filter (fun v => 3 ≤ bcv_T0.degree v)).card ≤ (Finset.univ.filter (fun v => bcv_T0.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bof2_bgnW_handshake_applies

/--
[bof2_interiorLeaf_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_interiorLeaf_witness_eq :
-- imply
  bof2_advT ≤ bof2_advG ∧ bof2_advG.degree 2 = 2 ∧ bof2_advT.degree 2 = 1 ∧ (2 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.bof2_interiorLeaf_witness

/--
[bof2_interiorLeaf_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_interiorLeaf_obstruction_eq :
-- imply
  ∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj) (B : Finset (Fin 4)), T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧ ¬ (∀ v, T.degree v = 1 → v ∈ B) := by
-- proof
  apply StatMech.Walls.bof2_interiorLeaf_obstruction

/--
[bof2_bk_of_treeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_bk_of_treeData_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bof2_bk_of_treeData p hp1 hp0 hdata

/--
[bof2_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean)
-/
@[path]
private lemma bof2_status_eq :
-- imply
  (∀ {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [_i : DecidableRel T.Adj], T.IsTree → (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card ≤ (Finset.univ.filter (fun v => T.degree v = 1)).card) ∧ (∀ {V : Type} [Fintype V] [DecidableEq V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj], T ≤ H → T.IsTree → ∀ {ι : Type} [Fintype ι] (f : ι → V), Function.Injective f → (∀ i, ∃ a₁ a₂ a₃ : V, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧ ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₂ ∧ ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₃ ∧ ¬ (bkg_deleteVertex H (f i)).Reachable a₂ a₃) → ∀ (B : Finset V), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧ (∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj) (B : Finset (Fin 4)), T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧ ¬ (∀ v, T.degree v = 1 → v ∈ B)) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bof2_status


-- created on 2026-10-23
