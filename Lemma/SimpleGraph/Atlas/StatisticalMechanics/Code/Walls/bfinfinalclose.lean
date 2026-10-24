import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bfinfinalclose
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfin_bk_of_subforestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_bk_of_subforestData_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bfin_bk_of_subforestData p hp1 hp0 hdata

/--
[bfin_acyclic_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_acyclic_free_eq
  {T G : SimpleGraph V}
-- given
  (hT : T.IsAcyclic)
  (hle : G ≤ T) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bfin_acyclic_free hT hle

/--
[bfin_GnBranchRay_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_GnBranchRay_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w x : Site d}
  {R : ℕ}
-- given
  (hT : T ≤ bgn_Gn ω L)
  (hR : 1 ≤ R)
  (hwx : w ≠ x)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bfin_GnBranchRay_reaches_boundary ω L T hT hR hwx hw hinf

/--
[bfin_Gn_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_Gn_le_lattice_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ} :
-- imply
  bgn_Gn ω L ≤ hypercubicLattice d := by
-- proof
  apply StatMech.Walls.bfin_Gn_le_lattice ω L

/--
[bfin_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_datum_implies_count_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bfin_datum_implies_count ω L R h

/--
[bfin_datum_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_datum_of_noTrif_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (hR : 1 ≤ R)
  (hno : ∀ y, y ∈ box 2 R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bau_ArmSubforestData ω L R := by
-- proof
  apply StatMech.Walls.bfin_datum_of_noTrif ω L R hR hno

/--
[bfin_bk_of_globalArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_bk_of_globalArmForest_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bfin_GlobalArmForest ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bfin_bk_of_globalArmForest p hp1 hp0 hdata

/--
[bfin_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean)
-/
@[path]
private lemma bfin_status_eq :
-- imply
  (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧ (∀ {V : Type} {T G : SimpleGraph V}, T.IsAcyclic → G ≤ T → G.IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), 1 ≤ R → (∀ y, y ∈ box 2 R → ¬ bc67_IsGnTrifurcation ω L y) → bau_ArmSubforestData ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
-- proof
  apply StatMech.Walls.bfin_status


-- created on 2026-10-23
