import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc109finiteenergy
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc109_precursor_pp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc109finiteenergy.lean)
-/
@[path]
private lemma bc109_precursor_pp_eq
  {d : ℕ}
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bc109_precursor_pp p hp1 hp0 L a₁ a₂ a₃ b₁ b₂ b₃ hpos

/--
[bc109_coarseTrifExistence_pp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc109finiteenergy.lean)
-/
@[path]
private lemma bc109_coarseTrifExistence_pp_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L := by
-- proof
  apply StatMech.Walls.bc109_coarseTrifExistence_pp p hp1 hp0 L hcoarseRoute

/--
[bc109_bk_count_half_pp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc109finiteenergy.lean)
-/
@[path]
private lemma bc109_bk_count_half_pp_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1))
  (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
  (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc109_bk_count_half_pp hd p hp1 hp0 hinv L hGlobal hcoarseRoute

/--
[bc109_precursor_witness_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc109finiteenergy.lean)
-/
@[path]
private lemma bc109_precursor_witness_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3) (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) := by
-- proof
  apply StatMech.Walls.bc109_precursor_witness_upperLines hL

/--
[bc109_precursor_forced_coarseTrif_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc109finiteenergy.lean)
-/
@[path]
private lemma bc109_precursor_forced_coarseTrif_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation (forceOpenFinset {s(bc57_pt (L : ℤ) 1, bc57_pt ((L : ℤ) + 1) 1), s(bc57_pt (L : ℤ) 2, bc57_pt ((L : ℤ) + 1) 2), s(bc57_pt (L : ℤ) 3, bc57_pt ((L : ℤ) + 1) 3)} bc60_upperLines) L 0 := by
-- proof
  apply StatMech.Walls.bc109_precursor_forced_coarseTrif_upperLines hL

/--
[bc109_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc109finiteenergy.lean)
-/
@[path]
private lemma bc109_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  (∀ (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d), 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧ (∀ (L : ℕ), (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) → bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L) ∧ (∀ (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)) (L : ℕ), (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) → (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) → bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc109_status hd p hp1 hp0


-- created on 2026-10-23
