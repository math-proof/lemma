import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkwburtonkeane
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bkw_lemma26_insertion_tolerance_pp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkwburtonkeane.lean)
-/
@[path]
private lemma bkw_lemma26_insertion_tolerance_pp_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
-- imply
  ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bkw_lemma26_insertion_tolerance_pp μ hinv hfe htop

/--
[bkw_count_half_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkwburtonkeane.lean)
-/
@[path]
private lemma bkw_count_half_of_forest_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
-- imply
  μ {ω | numInfiniteClusters 2 ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bkw_count_half_of_forest μ hinv hfe hforest

/--
[bkw_bk_uniqueness_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkwburtonkeane.lean)
-/
@[path]
private lemma bkw_bk_uniqueness_of_forest_eq
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bkw_bk_uniqueness_of_forest p hp1 hp0 hforest

/--
[bkw_top_null_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkwburtonkeane.lean)
-/
@[path]
private lemma bkw_top_null_of_forest_eq
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bkw_top_null_of_forest p hp1 hp0 hforest

/--
[bkw_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkwburtonkeane.lean)
-/
@[path]
private lemma bkw_status_eq
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], IsTranslationInvariant (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ → 0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], IsTranslationInvariant (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ ((∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bkw_status p hp1 hp0


-- created on 2026-10-23
