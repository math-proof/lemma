import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc115severance
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc115_coarsePrecursor_of_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_coarsePrecursor_of_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
  {ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc61_IsCoarseTrifurcation ω' L 0) :
-- imply
  ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, ω' ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ := by
-- proof
  apply StatMech.Walls.bc115_coarsePrecursor_of_coarseTrif L h

/--
[bc115_disconnected_of_distinctClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_disconnected_of_distinctClusters_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hne : cluster d ω x ≠ cluster d ω y) :
-- imply
  ¬ Connected d (removeSites T ω) x y := by
-- proof
  apply StatMech.Walls.bc115_disconnected_of_distinctClusters T ω hne

/--
[bc115_coarseTrif_disconnection_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_coarseTrif_disconnection_free_eq
  {d : ℕ}
  {L : ℕ}
  {ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc61_IsCoarseTrifurcation ω' L 0) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L 0) ω') a₂ a₃ := by
-- proof
  apply StatMech.Walls.bc115_coarseTrif_disconnection_free L h

/--
[bc115_coarseBoxAttach_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_coarseBoxAttach_of_merge_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (hmerge : bc115_CoarseTrifMerge d L n) :
-- imply
  bc111_CoarseBoxAttach d L n := by
-- proof
  apply StatMech.Walls.bc115_coarseBoxAttach_of_merge hmerge

/--
[bc115_hcoarseRoute_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_hcoarseRoute_of_merge_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmerge : ∀ n : ℕ, bc115_CoarseTrifMerge d L n) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
-- proof
  apply StatMech.Walls.bc115_hcoarseRoute_of_merge μ hfe L hmerge

/--
[bc115_coarseTrifExistence_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_coarseTrifExistence_of_merge_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmerge : ∀ n : ℕ, bc115_CoarseTrifMerge d L n) :
-- imply
  bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bc115_coarseTrifExistence_of_merge μ hfe L hmerge

/--
[bc115_forceOpen_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_forceOpen_empty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
-- proof
  apply StatMech.Walls.bc115_forceOpen_empty ω

/--
[bc115_merge_upperLines_emptyWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_merge_upperLines_emptyWiring_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ W : Finset (Sym2 (Site 2)), bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L 0 := by
-- proof
  apply StatMech.Walls.bc115_merge_upperLines_emptyWiring hL

/--
[bc115_precursor_upperLines_via_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_precursor_upperLines_via_merge_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2) (W : Finset (Sym2 (Site 2))), forceOpenFinset W bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃ := by
-- proof
  apply StatMech.Walls.bc115_precursor_upperLines_via_merge hL

/--
[bc115_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc115severance.lean)
-/
@[path]
private lemma bc115_status_eq
  {d : ℕ} :
-- imply
  (∀ (L : ℕ) (ω' : ConfigSpace (Sym2 (Site d))), bc61_IsCoarseTrifurcation ω' L 0 → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, ω' ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) ∧ (∀ (L n : ℕ), bc115_CoarseTrifMerge d L n → bc111_CoarseBoxAttach d L n) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), HasFiniteEnergyMerge μ → (∀ n : ℕ, bc115_CoarseTrifMerge 2 L n) → (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2, 0 < μ (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) ∧ bc61_CoarseTrifExistence μ L) ∧ (∀ (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d), cluster d ω x ≠ cluster d ω y → ¬ Connected d (removeSites T ω) x y) ∧ (∀ {L : ℕ}, 3 ≤ L → ∃ W : Finset (Sym2 (Site 2)), bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L 0) := by
-- proof
  apply StatMech.Walls.bc115_status


-- created on 2026-10-23
