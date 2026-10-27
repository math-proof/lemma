import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc91hcanonfree
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc91_upperLines_coarse_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_upperLines_coarse_at_zero_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc91_upperLines_coarse_at_zero hL

/--
[bc91_upperLines_not_genuine_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_upperLines_not_genuine_at_zero_eq
  {d : ℕ} :
-- imply
  ¬ bc89_GenuineTrif 2 bc60_upperLines (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc91_upperLines_not_genuine_at_zero

/--
[bc91_coarse_notImp_genuine_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_coarse_notImp_genuine_at_zero_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc89_GenuineTrif 2 bc60_upperLines (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc91_coarse_notImp_genuine_at_zero hL

/--
[bc91_coarse_imp_genuine_FALSE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_coarse_imp_genuine_FALSE_eq
  {d : ℕ} :
-- imply
  ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y → bc89_GenuineTrif 2 ω y) := by
-- proof
  apply StatMech.Walls.bc91_coarse_imp_genuine_FALSE

/--
[bc91_isTrif_not_genuine_at_zeroOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_isTrif_not_genuine_at_zeroOne_eq
  {d : ℕ} :
-- imply
  IsTrifurcation 2 bc60_upperLines (bc57_pt 0 1) ∧ ¬ bc89_GenuineTrif 2 bc60_upperLines (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bc91_isTrif_not_genuine_at_zeroOne

/--
[bc91_isTrif_imp_genuine_FALSE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_isTrif_imp_genuine_FALSE_eq
  {d : ℕ} :
-- imply
  ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) := by
-- proof
  apply StatMech.Walls.bc91_isTrif_imp_genuine_FALSE

/--
[bc91_mem_boxAround_zero_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_mem_boxAround_zero_scale_eq
  {d : ℕ}
  {x v : Site d} :
-- imply
  v ∈ bc61_boxAround d 0 x ↔ v = x := by
-- proof
  apply StatMech.Walls.bc91_mem_boxAround_zero_scale

/--
[bc91_removeSites_boxZero_eq_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_removeSites_boxZero_eq_removeSite_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites (bc61_boxAround d 0 x) ω = removeSite x ω := by
-- proof
  apply StatMech.Walls.bc91_removeSites_boxZero_eq_removeSite x ω

/--
[bc91_genuine_imp_coarse_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_genuine_imp_coarse_scale_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : bc89_GenuineTrif d ω x) :
-- imply
  bc61_IsCoarseTrifurcation ω 0 x := by
-- proof
  apply StatMech.Walls.bc91_genuine_imp_coarse_scale ω x h

/--
[bc91_hcanon_not_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_hcanon_not_free_eq
  {d : ℕ} :
-- imply
  (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y → bc89_GenuineTrif 2 ω y)) ∧ (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), bc89_GenuineTrif 2 ω x → bc61_IsCoarseTrifurcation ω 0 x) := by
-- proof
  apply StatMech.Walls.bc91_hcanon_not_free

/--
[bc91_as_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_as_residue_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bc91_as_residue μ L bdry hexp hbound hvol hdens

/--
[bc91_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc91hcanonfree.lean)
-/
@[path]
private lemma bc91_status_eq
  {d : ℕ} :
-- imply
  (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y → bc89_GenuineTrif 2 ω y)) ∧ (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc89_GenuineTrif 2 bc60_upperLines (0 : Site 2)) ∧ (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), bc89_GenuineTrif 2 ω x → bc61_IsCoarseTrifurcation ω 0 x) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ), (∀ R : ℕ, ((boxFinsetBK 2 R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R) → (∀ R, 0 < (boxFinsetBK 2 R).card) → Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0) → μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) := by
-- proof
  apply StatMech.Walls.bc91_status


-- created on 2026-10-23
