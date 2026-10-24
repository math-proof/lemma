import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc120closure
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc120_kne_top_of_top_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_kne_top_of_top_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0) :
-- imply
  ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
-- proof
  apply StatMech.Walls.bc120_kne_top_of_top_null μ htop

/--
[bc120_merge_null_of_top_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_merge_null_of_top_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0) :
-- imply
  μ (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.Walls.bc120_merge_null_of_top_null μ herg hfe htop

/--
[bc120_uniqueness_of_top_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_uniqueness_of_top_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc120_uniqueness_of_top_null μ herg hfe htop

/--
[bc120_bk_uniqueness_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_bk_uniqueness_of_residues_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
  (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc120_bk_uniqueness_of_residues hd p hp1 hp0 L hGlobal hcoarseRoute

/--
[bc120_top_null_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_top_null_of_residues_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
  (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc120_top_null_of_residues hd p hp1 hp0 L hGlobal hcoarseRoute

/--
[bc120_bk_uniqueness_via_bc73](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_bk_uniqueness_via_bc73_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc120_bk_uniqueness_via_bc73 hd p hp1 hp0 L hexp hforest hexist

/--
[bc120_bc73_of_bc69](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_bc73_of_bc69_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc120_bc73_of_bc69 ω L R h

/--
[bc120_gap1_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_gap1_discharged_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.bc120_gap1_discharged hd ω L R hL

/--
[bc120_armCovered_of_H1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_armCovered_of_H1_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {B H : Site d → Prop}
-- given
  (hmem : bc116_ArmPathMembership ω L y B H) :
-- imply
  bc114_ArmCovered (bc67_contractedLattice ω L y) B H := by
-- proof
  apply StatMech.Walls.bc120_armCovered_of_H1 ω L y hmem

/--
[bc120_full_separated_iff_gap2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_full_separated_iff_gap2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.bc120_full_separated_iff_gap2 ω L R

/--
[bc120_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc120closure.lean)
-/
@[path]
private lemma bc120_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ], IsErgodic (G := Multiplicative (Site d)) μ → HasFiniteEnergyMerge μ → μ {ω | numInfiniteClusters d ω = ⊤} = 0 → (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧ (∀ (L : ℕ) (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R), (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) → bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) := by
-- proof
  apply StatMech.Walls.bc120_status hd p hp1 hp0


-- created on 2026-10-23
