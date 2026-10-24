import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc111routing
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc111_measurableSet_coarsePrecursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_measurableSet_coarsePrecursor_eq
  {d : ℕ}
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d} :
-- imply
  MeasurableSet (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
-- proof
  apply StatMech.Walls.bc111_measurableSet_coarsePrecursor L a₁ a₂ a₃ b₁ b₂ b₃

/--
[bc111_coarseBoxRoute_of_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_coarseBoxRoute_of_attach_eq
  {d : ℕ}
  {L n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hres : bc111_CoarseBoxAttach d L n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) (W : Finset (Sym2 (Site d))), forceOpenFinset W ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ := by
-- proof
  apply StatMech.Walls.bc111_coarseBoxRoute_of_attach hres hω

/--
[bc111_precursorCover_of_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_precursorCover_of_attach_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (hres : bc111_CoarseBoxAttach d L n) :
-- imply
  threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (b₁ : Site d) (b₂ : Site d) (b₃ : Site d) (W : Finset (Sym2 (Site d))), (fun ω => forceOpenFinset W ω) ⁻¹' bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ := by
-- proof
  apply StatMech.Walls.bc111_precursorCover_of_attach hres

/--
[bc111_hcoarseRoute_at_of_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_hcoarseRoute_at_of_attach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L n : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hres : bc111_CoarseBoxAttach d L n)
  (hpos : 0 < μ (threeMeetBox d n)) :
-- imply
  ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
-- proof
  apply StatMech.Walls.bc111_hcoarseRoute_at_of_attach μ hfe hres hpos

/--
[bc111_hcoarseRoute_of_coarseAttach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_hcoarseRoute_of_coarseAttach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hres : ∀ n : ℕ, bc111_CoarseBoxAttach d L n) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
-- proof
  apply StatMech.Walls.bc111_hcoarseRoute_of_coarseAttach μ hfe L hres

/--
[bc111_coarseTrifExistence_of_coarseAttach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_coarseTrifExistence_of_coarseAttach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hres : ∀ n : ℕ, bc111_CoarseBoxAttach d L n) :
-- imply
  bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bc111_coarseTrifExistence_of_coarseAttach μ hfe L hres

/--
[bc111_coarsePrecursor_upperLines_emptyWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_coarsePrecursor_upperLines_emptyWiring_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  forceOpenFinset (∅ : Finset (Sym2 (Site 2))) bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3) (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) := by
-- proof
  apply StatMech.Walls.bc111_coarsePrecursor_upperLines_emptyWiring hL

/--
[bc111_coarseBoxRoute_upperLines_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_coarseBoxRoute_upperLines_witness_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2) (W : Finset (Sym2 (Site 2))), forceOpenFinset W bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃ := by
-- proof
  apply StatMech.Walls.bc111_coarseBoxRoute_upperLines_witness hL

/--
[bc111_coarsePrecursor_forces_boxAdjacency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_coarsePrecursor_forces_boxAdjacency_eq
  {d : ℕ}
  {L : ℕ}
  {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) :
-- imply
  (b₁ ∈ bc61_boxAround d L 0 ∧ (hypercubicLattice d).Adj b₁ a₁) ∧ (b₂ ∈ bc61_boxAround d L 0 ∧ (hypercubicLattice d).Adj b₂ a₂) ∧ (b₃ ∈ bc61_boxAround d L 0 ∧ (hypercubicLattice d).Adj b₃ a₃) := by
-- proof
  apply StatMech.Walls.bc111_coarsePrecursor_forces_boxAdjacency L a₁ a₂ a₃ b₁ b₂ b₃ ω hω

/--
[bc111_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean)
-/
@[path]
private lemma bc111_status_eq
  {d : ℕ} :
-- imply
  (∀ (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2), MeasurableSet (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), HasFiniteEnergyMerge μ → (∀ n : ℕ, bc111_CoarseBoxAttach 2 L n) → 0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site 2, 0 < μ (bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃)) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), HasFiniteEnergyMerge μ → (∀ n : ℕ, bc111_CoarseBoxAttach 2 L n) → bc61_CoarseTrifExistence μ L) ∧ (∀ {L : ℕ}, 3 ≤ L → ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site 2) (W : Finset (Sym2 (Site 2))), forceOpenFinset W bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L a₁ a₂ a₃ b₁ b₂ b₃) := by
-- proof
  apply StatMech.Walls.bc111_status


-- created on 2026-10-23
