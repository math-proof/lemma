import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc66assembly
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc66_coarseTrif_arms_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_coarseTrif_arms_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a : Site d}
-- given
  (hR : 1 ≤ R)
  (habox : a ∈ box d R)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z := by
-- proof
  apply StatMech.Walls.bc66_coarseTrif_arms_reach ω L R hR y a habox hinf

/--
[bc66_leaf_boundary_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_leaf_boundary_injection_eq
  {d : ℕ}
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {R : ℕ}
  {lam : W → Site d}
-- given
  (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d R)
  (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
-- imply
  (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc66_leaf_boundary_injection G R lam hmap hinj

/--
[bc66_connected_leaf_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_connected_leaf_count_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc66_connected_leaf_count G hacyc hmin

/--
[bc66_connectedForest_of_forestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_connectedForest_of_forestData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {W : Type}
  [Fintype W]
  [Nonempty W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {ιT : Site d → W}
  {lamL : W → Site d}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → 3 ≤ G.degree (ιT y))
  (hιinj : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → ∀ z, z ∈ box d R → bc61_IsCoarseTrifurcation ω L z → ιT y = ιT z → y = z)
  (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
  (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc66_connectedForest_of_forestData ω L R W G ιT lamL hacyc hmin hdeg3 hιinj hlammap hlaminj

/--
[bc66_coarseForest_of_boundaryInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_coarseForest_of_boundaryInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc66_coarseForest_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

/--
[bc66_coarseTcount_le_boundary_of_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_coarseTcount_le_boundary_of_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc65_ConnectedCoarseForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc66_coarseTcount_le_boundary_of_connectedForest ω L R h

/--
[bc66_wholeBox_severs_adversary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_wholeBox_severs_adversary_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc66_wholeBox_severs_adversary hL

/--
[bc66_adversary_arm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_adversary_arm_reaches_boundary_eq
  {d : ℕ}
  {L R : ℕ}
  {h : ℤ}
-- given
  (hR : 1 ≤ R)
  (hh : 1 ≤ h)
  (hbox : bc57_pt ((L : ℤ) + 1) h ∈ box 2 R) :
-- imply
  ∃ z ∈ vertexBoundary 2 R, Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) (bc57_pt ((L : ℤ) + 1) h) z := by
-- proof
  apply StatMech.Walls.bc66_adversary_arm_reaches_boundary hR hh hbox

/--
[bc66_shared_boundary_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_shared_boundary_survives_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc66_shared_boundary_survives L

/--
[bc66_connectedForest_caterpillar2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_connectedForest_caterpillar2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y₀ y₁ : Site d}
  {lamL : Fin 6 → Site d}
-- given
  (hy₀box : y₀ ∈ box d R)
  (hy₁box : y₁ ∈ box d R)
  (hyne : y₀ ≠ y₁)
  (hy₀tri : bc61_IsCoarseTrifurcation ω L y₀)
  (hy₁tri : bc61_IsCoarseTrifurcation ω L y₁)
  (hpair : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = y₀ ∨ y = y₁)
  (hlammap : ∀ v, bc65_cat2G.degree v = 1 → lamL v ∈ vertexBoundary d R)
  (hlaminj : Set.InjOn lamL (univ.filter (fun v => bc65_cat2G.degree v = 1))) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc66_connectedForest_caterpillar2 ω L R hy₀box hy₁box hyne hy₀tri hy₁tri hpair lamL hlammap hlaminj

/--
[bc66_infiniteClusters_top_null_of_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_infiniteClusters_top_null_of_connectedForest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hconn : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc65_ConnectedCoarseForest ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc66_infiniteClusters_top_null_of_connectedForest μ hd hinv hfe L hconn hcoarseRoute

/--
[bc66_infiniteClusters_top_null_of_boundaryInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_infiniteClusters_top_null_of_boundaryInjection_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbdvertices : ∀ R : ℕ, ∃ z₀ z₁ : Site d, z₀ ∈ vertexBoundary d R ∧ z₁ ∈ vertexBoundary d R ∧ z₀ ≠ z₁)
  (hbinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc64_CoarseBoundaryInjection ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc66_infiniteClusters_top_null_of_boundaryInjection μ hd hinv hfe L hbdvertices hbinj hcoarseRoute

/--
[bc66_coarse_armReaching_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_coarse_armReaching_unconditional_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a : Site d}
-- given
  (hR : 1 ≤ R)
  (habox : a ∈ box d R)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z := by
-- proof
  apply StatMech.Walls.bc66_coarse_armReaching_unconditional ω L R hR y a habox hinf

/--
[bc66_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc66assembly.lean)
-/
@[path]
private lemma bc66_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → ∃ z ∈ vertexBoundary d R, Connected d (removeSites (bc61_boxAround d L y) ω) a z) ∧ (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → bc64_CoarseBoundaryInjection ω L R → bc65_ConnectedCoarseForest ω L R) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
-- proof
  apply StatMech.Walls.bc66_status


-- created on 2026-10-23
