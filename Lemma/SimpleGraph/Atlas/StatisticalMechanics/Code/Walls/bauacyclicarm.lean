import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bauacyclicarm.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bau_isAcyclic_of_le_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_isAcyclic_of_le_tree_eq
  {T G : SimpleGraph V}
-- given
  (hT : T.IsTree)
  (hle : G ≤ T) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bau_isAcyclic_of_le_tree hT hle

/--
[bau_isAcyclic_of_le_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_isAcyclic_of_le_acyclic_eq
  {T G : SimpleGraph V}
-- given
  (hT : T.IsAcyclic)
  (hle : G ≤ T) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bau_isAcyclic_of_le_acyclic hT hle

/--
[bau_exists_spanningTree_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_exists_spanningTree_infinite_eq
  {H : SimpleGraph V}
-- given
  (hH : H.Connected) :
-- imply
  ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree := by
-- proof
  apply StatMech.Walls.bau_exists_spanningTree_infinite hH

/--
[bau_armUnion_acyclic_of_spanningTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_armUnion_acyclic_of_spanningTree_eq
  {H G : SimpleGraph V}
  {T : SimpleGraph V}
-- given
  (hH : H.Connected)
  (hTH : T ≤ H)
  (hT : T.IsTree)
  (hle : G ≤ T) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bau_armUnion_acyclic_of_spanningTree hH T hTH hT hle

/--
[bau_blf_of_subforestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_blf_of_subforestData_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  blf_AcyclicArmUnion ω L R := by
-- proof
  apply StatMech.Walls.bau_blf_of_subforestData ω L R h

/--
[bau_bc69_of_subforestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_bc69_of_subforestData_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bau_bc69_of_subforestData ω L R h

/--
[bau_bk_of_subforestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_bk_of_subforestData_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bau_bk_of_subforestData p hp1 hp0 hdata

/--
[bau_star_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_star_witness_eq :
-- imply
  bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3 ∧ bau_star.degree 1 = 1 ∧ bau_star.degree 2 = 1 ∧ bau_star.degree 3 = 1 := by
-- proof
  apply StatMech.Walls.bau_star_witness

/--
[bau_sub_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_sub_witness_eq :
-- imply
  bau_sub ≤ bau_star ∧ bau_sub ≠ bau_star ∧ bau_sub.IsAcyclic := by
-- proof
  apply StatMech.Walls.bau_sub_witness

/--
[bau_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean)
-/
@[path]
private lemma bau_status_eq :
-- imply
  (∀ {V : Type} {T G : SimpleGraph V}, T.IsTree → G ≤ T → G.IsAcyclic) ∧ (∀ {V : Type} {H : SimpleGraph V}, H.Connected → ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R → blf_AcyclicArmUnion ω L R) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧ (bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3) := by
-- proof
  apply StatMech.Walls.bau_status


-- created on 2026-10-23
