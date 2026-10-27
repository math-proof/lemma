import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bgctrifgraph.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bgc_adj_of_openAdj_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_adj_of_openAdj_avoiding_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {t a b : Site d}
-- given
  (hab : (openSubgraph d ω).Adj a b)
  (hta : a ∉ bc61_boxAround d L t)
  (htb : b ∉ bc61_boxAround d L t) :
-- imply
  (bc67_contractedLattice ω L t).Adj a b := by
-- proof
  apply StatMech.Walls.bgc_adj_of_openAdj_avoiding ω L t a b hab hta htb

/--
[bgc_reach_of_openAdj_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_reach_of_openAdj_avoiding_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {t a b : Site d}
-- given
  (hab : (openSubgraph d ω).Adj a b)
  (hta : a ∉ bc61_boxAround d L t)
  (htb : b ∉ bc61_boxAround d L t) :
-- imply
  (bc67_contractedLattice ω L t).Reachable a b := by
-- proof
  apply StatMech.Walls.bgc_reach_of_openAdj_avoiding ω L t a b hab hta htb

/--
[bgc_globalForest_of_trifForestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_globalForest_of_trifForestData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bgc_TrifForestData ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bgc_globalForest_of_trifForestData ω L R h

/--
[bgc_coarseTcount_of_trifForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_coarseTcount_of_trifForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bgc_TrifForestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bgc_coarseTcount_of_trifForest ω L R h

/--
[bgc_bc69_of_trifForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_bc69_of_trifForest_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)), bgc_TrifForestData ω L R) :
-- imply
  ∀ ω : ConfigSpace (Sym2 (Site d)), bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bgc_bc69_of_trifForest L R hdata

/--
[bgc_bk_uniqueness_of_trifForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_bk_uniqueness_of_trifForest_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bgc_bk_uniqueness_of_trifForest p hp1 hp0 hdata

/--
[bgc_top_null_of_trifForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_top_null_of_trifForest_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bgc_top_null_of_trifForest p hp1 hp0 hdata

/--
[bgc_trifForestData_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_trifForestData_of_noTrif_eq
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
  bgc_TrifForestData ω L R := by
-- proof
  apply StatMech.Walls.bgc_trifForestData_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bgc_trifForestData_of_singleStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_trifForestData_of_singleStar_eq
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
  (hainj : Function.Injective a)
  (hsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
  (hroute : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) :
-- imply
  bgc_TrifForestData ω L R := by
-- proof
  apply StatMech.Walls.bgc_trifForestData_of_singleStar ω L R a hxbox hxtri hsingle habdry hxne hainj hsep hroute

/--
[bgc_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean)
-/
@[path]
private lemma bgc_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bgc_TrifForestData ω L R → bc69_Gn_globalForest ω L R) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (t a b : Site d), (openSubgraph d ω).Adj a b → a ∉ bc61_boxAround d L t → b ∉ bc61_boxAround d L t → (bc67_contractedLattice ω L t).Reachable a b) := by
-- proof
  apply StatMech.Walls.bgc_status


-- created on 2026-10-23
