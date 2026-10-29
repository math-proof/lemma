import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfaforestassemble
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfa_notin_support_of_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_notin_support_of_isolated_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {t : V}
-- given
  (hiso : ∀ z, ¬ H.Adj t z) :
-- imply
  ∀ {a b : V} (w : H.Walk a b), a ≠ t → t ∉ w.support := by
-- proof
  apply StatMech.Walls.bfa_notin_support_of_isolated hiso

/--
[bfa_singleVertexCut_of_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_singleVertexCut_of_acyclic_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {t a b : V}
-- given
  (hG : G.IsAcyclic)
  (hta : G.Adj t a)
  (htb : G.Adj t b)
  (hab : a ≠ b) :
-- imply
  ¬ (bkg_deleteVertex G t).Reachable a b := by
-- proof
  apply StatMech.Walls.bfa_singleVertexCut_of_acyclic G hG t a b hta htb hab

/--
[bfa_classicalForestData_of_bc69](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_classicalForestData_of_bc69_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bkg_ClassicalForestData ω L R := by
-- proof
  apply StatMech.Walls.bfa_classicalForestData_of_bc69 ω L R h

/--
[bfa_classical_iff_bc69](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_classical_iff_bc69_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bfa_classical_iff_bc69 ω L R

/--
[bfa_classicalForestData_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_classicalForestData_of_noTrif_eq
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
  bkg_ClassicalForestData ω L R := by
-- proof
  apply StatMech.Walls.bfa_classicalForestData_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bfa_classicalForestData_of_singleStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_classicalForestData_of_singleStar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d R)
  (hxtri : bc67_IsGnTrifurcation ω L x)
  (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
  (habdry : ∀ i, a i ∈ vertexBoundary d R)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a) :
-- imply
  bkg_ClassicalForestData ω L R := by
-- proof
  apply StatMech.Walls.bfa_classicalForestData_of_singleStar ω L R a hxbox hxtri hsingle habdry hxne hainj

/--
[bfa_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_datum_implies_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bkg_ClassicalForestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bfa_datum_implies_count ω L R h

/--
[bfa_bk_of_classicalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_bk_of_classicalForest_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bfa_bk_of_classicalForest p hp1 hp0 hdata

/--
[bfa_bk_of_bc69Forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_bk_of_bc69Forest_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bfa_bk_of_bc69Forest p hp1 hp0 hdata

/--
[bfa_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfaforestassemble.lean)
-/
@[path]
private lemma bfa_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bkg_ClassicalForestData ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bkg_ClassicalForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bfa_status


-- created on 2026-10-23
