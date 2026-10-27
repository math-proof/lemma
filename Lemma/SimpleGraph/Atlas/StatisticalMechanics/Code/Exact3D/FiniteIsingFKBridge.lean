import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
open Filter MeasureTheory StatMech StatMech.Exact3D


/--
[finiteIsingXAxisTwoPointInVolume_eq_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma finiteIsingXAxisTwoPointInVolume_eq_of_le_eq
  {β : ℝ}
  {N n : ℕ}
-- given
  (hn : n ≤ N) :
-- imply
  finiteIsingXAxisTwoPointInVolume β N n = finiteIsingXAxisTwoPointInBox β N n hn := by
-- proof
  apply StatMech.Exact3D.finiteIsingXAxisTwoPointInVolume_eq_of_le hn

/--
[finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_q2_eq
  {d N : ℕ}
  {β : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < IsingFK.pOfBeta β)
  (hp1 : IsingFK.pOfBeta β < 1) :
-- imply
  (∑ σ : ConfigSpace (boxVerts d N), Ising.isingProb (boxGraph d N) β 0 σ * (Ising.spin σ x * Ising.spin σ y)) = (freeFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) := by
-- proof
  apply StatMech.Exact3D.finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_q2 d N β hp hp1 x y

/--
[finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos_eq
  {d N : ℕ}
  {β : ℝ}
  {x y : boxVerts d N}
-- given
  (hβ : 0 < β) :
-- imply
  (∑ σ : ConfigSpace (boxVerts d N), Ising.isingProb (boxGraph d N) β 0 σ * (Ising.spin σ x * Ising.spin σ y)) = (freeFiniteMeasure d N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) := by
-- proof
  apply StatMech.Exact3D.finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos d N hβ x y

/--
[finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β) :
-- imply
  finiteIsingXAxisTwoPointBox β n = freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) n := by
-- proof
  apply StatMech.Exact3D.finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2 hβ n

/--
[finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2_eq
  {β : ℝ}
  {N n : ℕ}
-- given
  (hβ : 0 < β) :
-- imply
  finiteIsingXAxisTwoPointInVolume β N n = freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
-- proof
  apply StatMech.Exact3D.finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2 hβ N n

/--
[freeFullVolumeQ2ThermodynamicLimitToIsing_of_finiteIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeFullVolumeQ2ThermodynamicLimitToIsing_of_finiteIsing_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
-- imply
  FreeFullVolumeQ2ThermodynamicLimitToIsing β hβ := by
-- proof
  apply StatMech.Exact3D.freeFullVolumeQ2ThermodynamicLimitToIsing_of_finiteIsing hβ hIsing

/--
[freeInfiniteVolumeXAxisConnectionOfBetaQ2_le_freeTwoPoint_of_finiteIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeInfiniteVolumeXAxisConnectionOfBetaQ2_le_freeTwoPoint_of_finiteIsing_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
-- imply
  ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤ := by
-- proof
  apply StatMech.Exact3D.freeInfiniteVolumeXAxisConnectionOfBetaQ2_le_freeTwoPoint_of_finiteIsing hβ hIsing

/--
[tendsto_freeQ2BoundaryProfileOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma tendsto_freeQ2BoundaryProfileOfBeta_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds (fkTheta 3 (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))) := by
-- proof
  apply StatMech.Exact3D.tendsto_freeQ2BoundaryProfileOfBeta β hβ

/--
[tendsto_freeQ2BoundaryProfileOfBeta_zero_of_fkTheta_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma tendsto_freeQ2BoundaryProfileOfBeta_zero_of_fkTheta_eq_zero_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hθ : fkTheta 3 (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) = 0) :
-- imply
  Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_freeQ2BoundaryProfileOfBeta_zero_of_fkTheta_eq_zero hβ hθ

/--
[tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_lt_fkPc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_lt_fkPc_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hpc : IsingFK.pOfBeta β < FK.fkPc 3 2) :
-- imply
  Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_lt_fkPc hβ hpc

/--
[tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_le_fkPc_of_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_le_fkPc_of_pc_eq
  {β : ℝ}
-- given
  (hθpc : ∀ (hp : 0 < FK.fkPc 3 2) (hp1 : FK.fkPc 3 2 < 1), FK.fkTheta 3 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hβ : 0 < β)
  (hpc : IsingFK.pOfBeta β ≤ FK.fkPc 3 2) :
-- imply
  Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_le_fkPc_of_pc hθpc hβ hpc

/--
[measureReal_boxBdryConnEvent_le_sum_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma measureReal_boxBdryConnEvent_le_sum_boxConnEvent_eq
  {d n : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))} :
-- imply
  μ.real (FK.boxBdryConnEvent d n) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts d n => FK.boxBoundary d n v), μ.real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) v) := by
-- proof
  apply StatMech.Exact3D.measureReal_boxBdryConnEvent_le_sum_boxConnEvent d n μ

/--
[wiredFiniteMeasure_real_boxBdryConnEvent_le_sum_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_boxBdryConnEvent_le_sum_boxConnEvent_eq
  {d n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ((FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxBdryConnEvent d n) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts d n => FK.boxBoundary d n v), ((FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) v) := by
-- proof
  apply StatMech.Exact3D.wiredFiniteMeasure_real_boxBdryConnEvent_le_sum_boxConnEvent d n hp hp1

/--
[wiredFiniteMeasure_real_boxBdryConnEvent_le_card_mul_of_forall_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_boxBdryConnEvent_le_card_mul_of_forall_boundary_eq
  {d n : ℕ}
  {p B : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hpoint : ∀ v : FK.boxVerts d n, FK.boxBoundary d n v → ((FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) v) ≤ B) :
-- imply
  ((FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxBdryConnEvent d n) ≤ ((Finset.univ.filter (fun v : FK.boxVerts d n => FK.boxBoundary d n v)).card : ℝ) * B := by
-- proof
  apply StatMech.Exact3D.wiredFiniteMeasure_real_boxBdryConnEvent_le_card_mul_of_forall_boundary d n hp hp1 hpoint

/--
[freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary_eq
  {β B : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hpoint : ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v → ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ B) :
-- imply
  freeQ2BoundaryProfileOfBeta β hβ n ≤ ((Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * B := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβ n hpoint

/--
[eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_of_eventually_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_of_eventually_boundary_eq
  {β : ℝ}
  {B : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hpoint : ∀ᶠ n in atTop, ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v → ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ B n) :
-- imply
  ∀ᶠ n in atTop, freeQ2BoundaryProfileOfBeta β hβ n ≤ ((Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * B n := by
-- proof
  apply StatMech.Exact3D.eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_of_eventually_boundary hβ hpoint

/--
[eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_exp_of_eventually_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_exp_of_eventually_boundary_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hpoint : ∀ᶠ n in atTop, ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v → ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ A n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  ∀ᶠ n in atTop, freeQ2BoundaryProfileOfBeta β hβ n ≤ (((Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * A n) * Real.exp (-(mass * (n : ℝ))) := by
-- proof
  apply StatMech.Exact3D.eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_exp_of_eventually_boundary hβ hpoint

/--
[freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume_le_profile_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume_le_profile_of_le_eq
  {β : ℝ}
  {N n : ℕ}
-- given
  (hβ : 0 < β)
  (hN : n ≤ N) :
-- imply
  freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n ≤ freeQ2BoundaryProfileOfBeta β hβ n := by
-- proof
  apply StatMech.Exact3D.freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume_le_profile_of_le β hβ hN

/--
[freeQ2FiniteVolumeBoundaryErrorBound_boxBoundaryConnProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeQ2FiniteVolumeBoundaryErrorBound_boxBoundaryConnProfile_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FreeQ2FiniteVolumeBoundaryErrorBound β hβ (freeQ2BoundaryProfileOfBeta β hβ) := by
-- proof
  apply StatMech.Exact3D.freeQ2FiniteVolumeBoundaryErrorBound_boxBoundaryConnProfile β hβ

/--
[freeQ2BoundaryErrorProfile_tendsto_zero_of_pOfBeta_lt_fkPc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeQ2BoundaryErrorProfile_tendsto_zero_of_pOfBeta_lt_fkPc_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hpc : IsingFK.pOfBeta β < FK.fkPc 3 2) :
-- imply
  FreeQ2FiniteVolumeBoundaryErrorBound β hβ (freeQ2BoundaryProfileOfBeta β hβ) ∧ Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryErrorProfile_tendsto_zero_of_pOfBeta_lt_fkPc hβ hpc

/--
[freeTwoPoint_le_freeInfiniteVolumeXAxisConnectionOfBetaQ2_add_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeTwoPoint_le_freeInfiniteVolumeXAxisConnectionOfBetaQ2_add_boundary_eq
  {β : ℝ}
  {B : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B) :
-- imply
  ∀ᶠ n in atTop, := by
-- proof
  apply StatMech.Exact3D.freeTwoPoint_le_freeInfiniteVolumeXAxisConnectionOfBetaQ2_add_boundary hβ hIsing hBoundary

/--
[freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint_eq
  {β : ℝ}
  {B : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B) :
-- imply
  ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤ := by
-- proof
  apply StatMech.Exact3D.freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint hβ hIsing hBoundary

/--
[freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint_profile_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
-- imply
  ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤ := by
-- proof
  apply StatMech.Exact3D.freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint_profile hβ hIsing

/--
[freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_additiveCompare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_additiveCompare_eq
  {β mass : ℝ}
  {B Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hcompare : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤ |freeTwoPointOnXAxis β n| ∧ |freeTwoPointOnXAxis β n| ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
  (hhi : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_additiveCompare hβ hcompare hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundary_eq
  {β mass : ℝ}
  {B Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
  (hhi : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundary hβ hIsing hBoundary hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryProfile_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
  (hhi : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + freeQ2BoundaryProfileOfBeta β hβ n ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryProfile hβ hIsing hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_profileSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_profileSeparate_eq
  {β mass : ℝ}
  {Alo AfkHi AprofHi Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hprofileHi : ∀ᶠ n in atTop, freeQ2BoundaryProfileOfBeta β hβ n ≤ AprofHi n * Real.exp (-(mass * (n : ℝ))))
  (hcombine : ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n) :
-- imply
  FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_profileSeparate hβ hIsing hconn hhi_pos hhi_log hprofileHi hcombine

/--
[freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryPointwise_eq
  {β mass : ℝ}
  {Alo AfkHi AbdryHi Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hboundaryPoint : ∀ᶠ n in atTop, ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v → ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ AbdryHi n * Real.exp (-(mass * (n : ℝ))))
  (hcombine : ∀ᶠ n in atTop, AfkHi n + ((Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * AbdryHi n ≤ Ahi n) :
-- imply
  FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryPointwise hβ hIsing hconn hhi_pos hhi_log hboundaryPoint hcombine

/--
[free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary_eq
  {β mass : ℝ}
  {B Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
  (hhi : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary hβ hIsing hBoundary hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary_eq
  {β mass : ℝ}
  {B Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hmass : 0 < mass)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
  (hhi : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary hβ hmass hIsing hBoundary hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
  (hhi : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + freeQ2BoundaryProfileOfBeta β hβ n ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile hβ hIsing hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hmass : 0 < mass)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
  (hhi : ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + freeQ2BoundaryProfileOfBeta β hβ n ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile hβ hmass hIsing hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate_eq
  {β mass : ℝ}
  {Alo AfkHi AprofHi Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hprofileHi : ∀ᶠ n in atTop, freeQ2BoundaryProfileOfBeta β hβ n ≤ AprofHi n * Real.exp (-(mass * (n : ℝ))))
  (hcombine : ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate hβ hIsing hconn hhi_pos hhi_log hprofileHi hcombine

/--
[free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate_eq
  {β mass : ℝ}
  {Alo AfkHi AprofHi Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hmass : 0 < mass)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hprofileHi : ∀ᶠ n in atTop, freeQ2BoundaryProfileOfBeta β hβ n ≤ AprofHi n * Real.exp (-(mass * (n : ℝ))))
  (hcombine : ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate hβ hmass hIsing hconn hhi_pos hhi_log hprofileHi hcombine

/--
[free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise_eq
  {β mass : ℝ}
  {Alo AfkHi AbdryHi Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hboundaryPoint : ∀ᶠ n in atTop, ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v → ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ AbdryHi n * Real.exp (-(mass * (n : ℝ))))
  (hcombine : ∀ᶠ n in atTop, AfkHi n + ((Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * AbdryHi n ≤ Ahi n) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise hβ hIsing hconn hhi_pos hhi_log hboundaryPoint hcombine

/--
[free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise_eq
  {β mass : ℝ}
  {Alo AfkHi AbdryHi Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hmass : 0 < mass)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hboundaryPoint : ∀ᶠ n in atTop, ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v → ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ AbdryHi n * Real.exp (-(mass * (n : ℝ))))
  (hcombine : ∀ᶠ n in atTop, AfkHi n + ((Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * AbdryHi n ≤ Ahi n) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise hβ hmass hIsing hconn hhi_pos hhi_log hboundaryPoint hcombine

/--
[freeXAxisQ2ConnectionAgrees_of_finiteVolume_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma freeXAxisQ2ConnectionAgrees_of_finiteVolume_restrictedCylinderComparison_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
  (hrestricted : FreeFiniteIsingFKXAxisRestrictedCylinderComparison β hβ) :
-- imply
  FreeXAxisQ2ConnectionAgrees β hβ := by
-- proof
  apply StatMech.Exact3D.freeXAxisQ2ConnectionAgrees_of_finiteVolume_restrictedCylinderComparison hβ hIsing hrestricted

/--
[fkXAxisConnectionExactExponentialDecay_freeFiniteVolumeQ2_iff_finiteIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma fkXAxisConnectionExactExponentialDecay_freeFiniteVolumeQ2_iff_finiteIsing_eq
  {β A m : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FKXAxisConnectionExactExponentialDecay (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m ↔ FKXAxisConnectionExactExponentialDecay (finiteIsingXAxisTwoPointBox β) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionExactExponentialDecay_freeFiniteVolumeQ2_iff_finiteIsing hβ

/--
[fkXAxisConnectionExactExponentialDecay_finiteIsing_iff_freeFiniteVolumeQ2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma fkXAxisConnectionExactExponentialDecay_finiteIsing_iff_freeFiniteVolumeQ2_eq
  {β A m : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FKXAxisConnectionExactExponentialDecay (finiteIsingXAxisTwoPointBox β) A m ↔ FKXAxisConnectionExactExponentialDecay (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionExactExponentialDecay_finiteIsing_iff_freeFiniteVolumeQ2 hβ

/--
[fkXAxisConnectionSubexponentialPrefactorDecay_freeFiniteVolumeQ2_iff_finiteIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma fkXAxisConnectionSubexponentialPrefactorDecay_freeFiniteVolumeQ2_iff_finiteIsing_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m ↔ FKXAxisConnectionSubexponentialPrefactorDecay (finiteIsingXAxisTwoPointBox β) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionSubexponentialPrefactorDecay_freeFiniteVolumeQ2_iff_finiteIsing hβ

/--
[fkXAxisConnectionSubexponentialPrefactorDecay_finiteIsing_iff_freeFiniteVolumeQ2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma fkXAxisConnectionSubexponentialPrefactorDecay_finiteIsing_iff_freeFiniteVolumeQ2_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (finiteIsingXAxisTwoPointBox β) A m ↔ FKXAxisConnectionSubexponentialPrefactorDecay (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionSubexponentialPrefactorDecay_finiteIsing_iff_freeFiniteVolumeQ2 hβ

/--
[fkXAxisConnectionTwoSidedSubexponentialBounds_freeFiniteVolumeQ2_iff_finiteIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma fkXAxisConnectionTwoSidedSubexponentialBounds_freeFiniteVolumeQ2_iff_finiteIsing_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) Alo Ahi m ↔ FKXAxisConnectionTwoSidedSubexponentialBounds (finiteIsingXAxisTwoPointBox β) Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionTwoSidedSubexponentialBounds_freeFiniteVolumeQ2_iff_finiteIsing hβ

/--
[fkXAxisConnectionTwoSidedSubexponentialBounds_finiteIsing_iff_freeFiniteVolumeQ2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean)
-/
@[path]
private lemma fkXAxisConnectionTwoSidedSubexponentialBounds_finiteIsing_iff_freeFiniteVolumeQ2_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (finiteIsingXAxisTwoPointBox β) Alo Ahi m ↔ FKXAxisConnectionTwoSidedSubexponentialBounds (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionTwoSidedSubexponentialBounds_finiteIsing_iff_freeFiniteVolumeQ2 hβ


-- created on 2026-10-23
