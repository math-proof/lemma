import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bcaconcreteclose
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bca_bk_of_subforestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_bk_of_subforestData_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bca_bk_of_subforestData p hp1 hp0 hdata

/--
[bca_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_datum_implies_count_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bca_datum_implies_count ω L R h

/--
[bca_datum_implies_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_datum_implies_globalForest_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bca_datum_implies_globalForest ω L R h

/--
[bca_fieldB_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_fieldB_free_eq
  {H : SimpleGraph V}
-- given
  (hH : H.Connected) :
-- imply
  ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree := by
-- proof
  apply StatMech.Walls.bca_fieldB_free hH

/--
[bca_fieldC_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_fieldC_free_eq
  {T G : SimpleGraph V}
-- given
  (hT : T.IsTree)
  (hle : G ≤ T) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bca_fieldC_free hT hle

/--
[bca_fieldD_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_fieldD_free_eq
  [Fintype V]
  {H T : SimpleGraph V}
  [DecidableRel T.Adj]
  {x a₁ a₂ a₃ : V}
-- given
  (hTH : T ≤ H)
  (hTconn : T.Connected)
  (hne₁ : a₁ ≠ x)
  (hne₂ : a₂ ≠ x)
  (hne₃ : a₃ ≠ x)
  (hsep₁₂ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₂)
  (hsep₁₃ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₃)
  (hsep₂₃ : ¬ (bkg_deleteVertex H x).Reachable a₂ a₃) :
-- imply
  3 ≤ T.degree x := by
-- proof
  apply StatMech.Walls.bca_fieldD_free hTH hTconn hne₁ hne₂ hne₃ hsep₁₂ hsep₁₃ hsep₂₃

/--
[bca_star_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_star_witness_eq :
-- imply
  bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3 ∧ bau_star.degree 1 = 1 ∧ bau_star.degree 2 = 1 ∧ bau_star.degree 3 = 1 := by
-- proof
  apply StatMech.Walls.bca_star_witness

/--
[bca_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcaconcreteclose.lean)
-/
@[path]
private lemma bca_status_eq :
-- imply
  (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧ (∀ {V : Type} {H : SimpleGraph V}, H.Connected → ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree) ∧ (∀ {V : Type} {T G : SimpleGraph V}, T.IsTree → G ≤ T → G.IsAcyclic) ∧ (bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3) := by
-- proof
  apply StatMech.Walls.bca_status


-- created on 2026-10-23
