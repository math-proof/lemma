import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc86finiteNcount
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc86_sublatticeForest_of_gnData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_sublatticeForest_of_gnData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hgn : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc86_sublatticeForest_of_gnData ω L R hgn

/--
[bc86_count_on_empty_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_count_on_empty_coarseTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hno : bc61_coarseTrifFinset ω L R = ∅) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc86_count_on_empty_coarseTrif ω L R hno

/--
[bc86_coarseTrif_is_branchpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_coarseTrif_is_branchpoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃ := by
-- proof
  apply StatMech.Walls.bc86_coarseTrif_is_branchpoint ω L h

/--
[bc86_singleBox_cut_free_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_singleBox_cut_free_of_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃ := by
-- proof
  apply StatMech.Walls.bc86_singleBox_cut_free_of_le_one ω L h

/--
[bc86_arms_connected_and_cut_disconnected_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_arms_connected_and_cut_disconnected_of_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃) ∧ (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc86_arms_connected_and_cut_disconnected_of_le_one ω L hN h

/--
[bc86_fiber_arms_can_coincide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_fiber_arms_can_coincide_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (h : bc61_IsCoarseTrifurcation ω L y)
  (h' : bc61_IsCoarseTrifurcation ω L y') :
-- imply
  ∃ a a' : Site d, (cluster d ω a).Infinite ∧ (cluster d ω a').Infinite ∧ Connected d ω a a' := by
-- proof
  apply StatMech.Walls.bc86_fiber_arms_can_coincide ω L hN h h'

/--
[bc86_count_holds_of_le_one_and_gnData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_count_holds_of_le_one_and_gnData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (hgn : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc86_count_holds_of_le_one_and_gnData ω L R hN hgn

/--
[bc86_upperLines_N_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_upperLines_N_top_eq
  {d : ℕ} :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc86_upperLines_N_top

/--
[bc86_ae_count_of_ae_gnData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_ae_count_of_ae_gnData_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hgn_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
-- imply
  ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc86_ae_count_of_ae_gnData μ L hgn_ae

/--
[bc86_bk_from_ae_gnData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_bk_from_ae_gnData_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hgn_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc86_bk_from_ae_gnData μ hd L hinv hgn_ae hexist

/--
[bc86_finiteN_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_finiteN_ae_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hgn_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω < ⊤} = 1 := by
-- proof
  apply StatMech.Walls.bc86_finiteN_ae μ hd L hinv hgn_ae hexist

/--
[bc86_upperLines_emptyFiber_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_upperLines_emptyFiber_count_eq
  {d : ℕ}
  {L R : ℕ}
  {c : Fin 2 → Fin (2 * L + 1)}
-- given
  (hR : 1 ≤ R)
  (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
-- imply
  (bc73_fiber bc60_upperLines L R c).card ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bc86_upperLines_emptyFiber_count hR c hempty

/--
[bc86_upperLines_gnCut_needs_buffer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_upperLines_gnCut_needs_buffer_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc86_upperLines_gnCut_needs_buffer L

/--
[bc86_cardinal_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_cardinal_verdict_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), (∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) → bc73_SublatticeForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (y : Site d), bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site d, ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧ ((∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc86_cardinal_verdict μ hd L hinv

/--
[bc86_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc86finiteNcount.lean)
-/
@[path]
private lemma bc86_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), (∀ c : Fin 2 → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) → bc73_SublatticeForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site 2, ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y y' : Site 2), numInfiniteClusters 2 ω ≤ 1 → bc61_IsCoarseTrifurcation ω L y → bc61_IsCoarseTrifurcation ω L y' → ∃ a a' : Site 2, (cluster 2 ω a).Infinite ∧ (cluster 2 ω a').Infinite ∧ Connected 2 ω a a') ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, ∀ c : Fin 2 → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc86_status


-- created on 2026-10-23
