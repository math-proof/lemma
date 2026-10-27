import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part5
open Filter MeasureTheory StatMech StatMech.Exact3D


/--
[freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2_eq
  {d N : ℕ}
  {p : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y)) atTop (nhds ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y))) := by
-- proof
  apply StatMech.Exact3D.freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2 d N hp hp1 x y

/--
[tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β) :
-- imply
  Tendsto (fun N => freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n) atTop (nhds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)) := by
-- proof
  apply StatMech.Exact3D.tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ n

/--
[freeFiniteMeasure_real_boxConnEvent_mono_outer_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_boxConnEvent_mono_outer_q2_eq
  {d : ℕ}
  {n M₁ M₂ : ℕ}
  {p : ℝ}
  {x y : boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hM₁ : n ≤ M₁)
  (hM : M₁ ≤ M₂) :
-- imply
  ((freeFiniteMeasure d M₁ hp hp1 (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d n x y) ≤ ((freeFiniteMeasure d M₂ hp hp1 (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d n x y) := by
-- proof
  apply StatMech.Exact3D.freeFiniteMeasure_real_boxConnEvent_mono_outer_q2 d hp hp1 hM₁ hM x y

/--
[boxConnEvent_subset_full_boxConnEvent_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma boxConnEvent_subset_full_boxConnEvent_of_le_eq
  {d : ℕ}
  {n N : ℕ}
  {x y : boxVerts d n}
-- given
  (h : n ≤ N) :
-- imply
  boxConnEvent d n x y ⊆ boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) := by
-- proof
  apply StatMech.Exact3D.boxConnEvent_subset_full_boxConnEvent_of_le d h x y

/--
[full_boxConnEvent_eq_inner_union_detour_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma full_boxConnEvent_eq_inner_union_detour_of_le_eq
  {d : ℕ}
  {n N : ℕ}
  {x y : boxVerts d n}
-- given
  (h : n ≤ N) :
-- imply
  boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) = boxConnEvent d n x y ∪ boxConnectionDetourEvent d h x y := by
-- proof
  apply StatMech.Exact3D.full_boxConnEvent_eq_inner_union_detour_of_le d h x y

/--
[measureReal_full_boxConnEvent_eq_inner_add_detour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma measureReal_full_boxConnEvent_eq_inner_add_detour_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))}
  [IsFiniteMeasure μ]
  {n N : ℕ}
  {x y : boxVerts d n}
-- given
  (h : n ≤ N) :
-- imply
  μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y)) = μ.real (boxConnEvent d n x y) + μ.real (boxConnectionDetourEvent d h x y) := by
-- proof
  apply StatMech.Exact3D.measureReal_full_boxConnEvent_eq_inner_add_detour d μ h x y

/--
[measureReal_full_boxConnEvent_le_inner_add_detour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma measureReal_full_boxConnEvent_le_inner_add_detour_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))}
  {n N : ℕ}
  {x y : boxVerts d n}
-- given
  (h : n ≤ N) :
-- imply
  μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y)) ≤ μ.real (boxConnEvent d n x y) + μ.real (boxConnectionDetourEvent d h x y) := by
-- proof
  apply StatMech.Exact3D.measureReal_full_boxConnEvent_le_inner_add_detour d μ h x y

/--
[boxVertInclLE_range_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma boxVertInclLE_range_iff_eq
  {d : ℕ}
  {n N : ℕ}
  {z : boxVerts d N}
-- given
  (h : n ≤ N) :
-- imply
  (∃ x : boxVerts d n, boxVertInclLE d h x = z) ↔ (z : Lattice.Site d) ∈ Lattice.box d n := by
-- proof
  apply StatMech.Exact3D.boxVertInclLE_range_iff d h z

/--
[openSub_boxRestrict_adj_boxVertInclLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma openSub_boxRestrict_adj_boxVertInclLE_eq
  {d : ℕ}
  {n N : ℕ}
  {ω : ConfigSpace (Sym2 (Lattice.Site d))}
  {x y : boxVerts d n}
-- given
  (h : n ≤ N) :
-- imply
  (openSub (boxGraph d N) (boxRestrict d N ω)).Adj (boxVertInclLE d h x) (boxVertInclLE d h y) ↔ (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
-- proof
  apply StatMech.Exact3D.openSub_boxRestrict_adj_boxVertInclLE d h ω x y

/--
[boxBoundary_of_openSub_adj_outer_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma boxBoundary_of_openSub_adj_outer_of_le_eq
  {d : ℕ}
  {n N : ℕ}
  {ω : ConfigSpace (Sym2 (Lattice.Site d))}
  {x : boxVerts d n}
  {z : boxVerts d N}
-- given
  (hn : 1 ≤ n)
  (h : n ≤ N)
  (hz : (z : Lattice.Site d) ∉ Lattice.box d n)
  (hadj : (openSub (boxGraph d N) (boxRestrict d N ω)).Adj (boxVertInclLE d h x) z) :
-- imply
  boxBoundary d n x := by
-- proof
  apply StatMech.Exact3D.boxBoundary_of_openSub_adj_outer_of_le d hn h ω hz hadj

/--
[connToBdry_of_outer_reachable_not_inner_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma connToBdry_of_outer_reachable_not_inner_of_le_eq
  {d : ℕ}
  {n N : ℕ}
  {ω : ConfigSpace (Sym2 (Lattice.Site d))}
  {y : boxVerts d n}
-- given
  (hn : 1 ≤ n)
  (h : n ≤ N)
  (houter : (openSub (boxGraph d N) (boxRestrict d N ω)).Reachable (boxVertInclLE d h (IsingFK.boxOrigin d n)) (boxVertInclLE d h y))
  (hnotInner : ¬ (openSub (boxGraph d n) (boxRestrict d n ω)).Reachable (IsingFK.boxOrigin d n) y) :
-- imply
  IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
-- proof
  apply StatMech.Exact3D.connToBdry_of_outer_reachable_not_inner_of_le d hn h ω y houter hnotInner

/--
[boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le_eq
  {d : ℕ}
  {n N : ℕ}
  {y : boxVerts d n}
-- given
  (hn : 1 ≤ n)
  (h : n ≤ N) :
-- imply
  boxConnectionDetourEvent d h (IsingFK.boxOrigin d n) y ⊆ boxBdryConnEvent d n := by
-- proof
  apply StatMech.Exact3D.boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le d hn h y

/--
[boxConnectionDetourEvent_subset_boxBdryConnEvent_xaxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma boxConnectionDetourEvent_subset_boxBdryConnEvent_xaxis_eq
  {n N : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : n ≤ N) :
-- imply
  boxConnectionDetourEvent 3 h (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n) ⊆ boxBdryConnEvent 3 n := by
-- proof
  apply StatMech.Exact3D.boxConnectionDetourEvent_subset_boxBdryConnEvent_xaxis hn h

/--
[freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_of_le_eq
  {β : ℝ}
  {N n : ℕ}
-- given
  (hβ : 0 < β)
  (hn : n ≤ N) :
-- imply
  freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n ≤ freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
-- proof
  apply StatMech.Exact3D.freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_of_le β hβ hn

/--
[eventually_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma eventually_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β) :
-- imply
  ∀ᶠ N in atTop, freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n ≤ freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
-- proof
  apply StatMech.Exact3D.eventually_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full β hβ n

/--
[freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le_eq
  {β : ℝ}
  {N n : ℕ}
-- given
  (hβ : 0 < β)
  (hnpos : 1 ≤ n)
  (hn : n ≤ N) :
-- imply
  freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤ freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n := by
-- proof
  apply StatMech.Exact3D.freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le β hβ hnpos hn

/--
[eventually_freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma eventually_freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hnpos : 1 ≤ n) :
-- imply
  ∀ᶠ N in atTop, freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤ freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n := by
-- proof
  apply StatMech.Exact3D.eventually_freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary β hβ n hnpos

/--
[freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le_eq
  {β : ℝ}
  {N n : ℕ}
-- given
  (hβ : 0 < β)
  (hn : n ≤ N) :
-- imply
  freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n + freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n := by
-- proof
  apply StatMech.Exact3D.freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le β hβ hn

/--
[eventually_freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma eventually_freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β) :
-- imply
  ∀ᶠ N in atTop, freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n + freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n := by
-- proof
  apply StatMech.Exact3D.eventually_freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour β hβ n

/--
[wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2_eq
  {d N : ℕ}
  {p : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y)) atTop (nhds ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y))) := by
-- proof
  apply StatMech.Exact3D.wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2 d N hp hp1 x y

/--
[freeInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2_eq
  {d N : ℕ}
  {p B : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) ≤ B) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) ≤ B := by
-- proof
  apply StatMech.Exact3D.freeInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2 d N hp hp1 x y hB

/--
[le_freeInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma le_freeInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2_eq
  {d N : ℕ}
  {p B : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, B ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y)) :
-- imply
  B ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) := by
-- proof
  apply StatMech.Exact3D.le_freeInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2 d N hp hp1 x y hB

/--
[wiredInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma wiredInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2_eq
  {d N : ℕ}
  {p B : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) ≤ B) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) ≤ B := by
-- proof
  apply StatMech.Exact3D.wiredInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2 d N hp hp1 x y hB

/--
[le_wiredInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma le_wiredInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2_eq
  {d N : ℕ}
  {p B : ℝ}
  {x y : boxVerts d N}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, B ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y)) :
-- imply
  B ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (boxConnEvent d N x y) := by
-- proof
  apply StatMech.Exact3D.le_wiredInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2 d N hp hp1 x y hB

/--
[freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le_eq
  {p B : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, (freeFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) ≤ B) :
-- imply
  freeInfiniteVolumeXAxisConnectionQ2 p hp hp1 n ≤ B := by
-- proof
  apply StatMech.Exact3D.freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le hp hp1 n hB

/--
[le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent_eq
  {p B : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, B ≤ (freeFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n))) :
-- imply
  B ≤ freeInfiniteVolumeXAxisConnectionQ2 p hp hp1 n := by
-- proof
  apply StatMech.Exact3D.le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent hp hp1 n hB

/--
[wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le_eq
  {p B : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, (wiredFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) ≤ B) :
-- imply
  wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1 n ≤ B := by
-- proof
  apply StatMech.Exact3D.wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le hp hp1 n hB

/--
[le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent_eq
  {p B : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hB : ∀ᶠ m in atTop, B ≤ (wiredFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n))) :
-- imply
  B ≤ wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1 n := by
-- proof
  apply StatMech.Exact3D.le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent hp hp1 n hB

/--
[fkTwoSidedFreeIVQ2_of_eventually_boxConnEvent_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkTwoSidedFreeIVQ2_of_eventually_boxConnEvent_bounds_eq
  {p mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, ∀ᶠ M in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)))
  (hhi : ∀ᶠ n in atTop, ∀ᶠ M in atTop, (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.fkTwoSidedFreeIVQ2_of_eventually_boxConnEvent_bounds hp hp1 hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds_eq
  {p mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, ∀ᶠ M in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)))
  (hhi : ∀ᶠ n in atTop, ∀ᶠ M in atTop, (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds hp hp1 hlo_pos hhi_pos hlo_log hhi_log hlo hhi

/--
[fkExactFreeIVQ2_of_eventually_boxConnEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkExactFreeIVQ2_of_eventually_boxConnEvent_eq_eq
  {p A mass : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (h : ∀ᶠ n in atTop, ∀ᶠ M in atTop, (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) = A * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
-- proof
  apply StatMech.Exact3D.fkExactFreeIVQ2_of_eventually_boxConnEvent_eq hp hp1 h

/--
[fkExactWiredIVQ2_of_eventually_boxConnEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkExactWiredIVQ2_of_eventually_boxConnEvent_eq_eq
  {p A mass : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (h : ∀ᶠ n in atTop, ∀ᶠ M in atTop, (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) = A * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
-- proof
  apply StatMech.Exact3D.fkExactWiredIVQ2_of_eventually_boxConnEvent_eq hp hp1 h

/--
[fkSubexpFreeIVQ2_of_eventually_boxConnEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkSubexpFreeIVQ2_of_eventually_boxConnEvent_eq_eq
  {p mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA_pos : ∀ᶠ n in atTop, 0 < A n)
  (hA_log : Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) atTop (nhds 0))
  (h : ∀ᶠ n in atTop, ∀ᶠ M in atTop, (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) = A n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
-- proof
  apply StatMech.Exact3D.fkSubexpFreeIVQ2_of_eventually_boxConnEvent_eq hp hp1 hA_pos hA_log h

/--
[fkSubexpWiredIVQ2_of_eventually_boxConnEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkSubexpWiredIVQ2_of_eventually_boxConnEvent_eq_eq
  {p mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA_pos : ∀ᶠ n in atTop, 0 < A n)
  (hA_log : Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) atTop (nhds 0))
  (h : ∀ᶠ n in atTop, ∀ᶠ M in atTop, (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) = A n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
-- proof
  apply StatMech.Exact3D.fkSubexpWiredIVQ2_of_eventually_boxConnEvent_eq hp hp1 hA_pos hA_log h

/--
[fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
-- proof
  apply StatMech.Exact3D.fkExactFreeIVQ2_of_freeFiniteVolumeExactOfBeta hβpos hexact

/--
[fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
-- proof
  apply StatMech.Exact3D.fkExactWiredIVQ2_of_wiredFiniteVolumeExactOfBeta hβpos hexact

/--
[fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hsubexp : FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
-- proof
  apply StatMech.Exact3D.fkSubexpFreeIVQ2_of_freeFiniteVolumeSubexpOfBeta hβpos hsubexp

/--
[fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hsubexp : WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A mass := by
-- proof
  apply StatMech.Exact3D.fkSubexpWiredIVQ2_of_wiredFiniteVolumeSubexpOfBeta hβpos hsubexp

/--
[fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hbounds : FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta hβpos hbounds

/--
[fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hbounds : WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi mass := by
-- proof
  apply StatMech.Exact3D.fkTwoSidedWiredIVQ2_of_wiredFiniteVolumeBoundsOfBeta hβpos hbounds

/--
[free_wired_multiOpen_eq_of_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_wired_multiOpen_eq_of_not_badP_q2_eq
  {d : ℕ}
  {p : ℝ}
  {T : Finset (Sym2 (Lattice.Site d))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ FK.fwa_badP d) :
-- imply
  (FK.freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.fmu_multiOpen T) = (FK.wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.fmu_multiOpen T) := by
-- proof
  apply StatMech.Exact3D.free_wired_multiOpen_eq_of_not_badP_q2 d hd hp hp1 hbad T

/--
[free_wired_multiOpen_eq_of_beta_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_wired_multiOpen_eq_of_beta_not_badP_q2_eq
  {d : ℕ}
  {β : ℝ}
  {T : Finset (Sym2 (Lattice.Site d))}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP d) :
-- imply
  (FK.freeInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.fmu_multiOpen T) = (FK.wiredInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.fmu_multiOpen T) := by
-- proof
  apply StatMech.Exact3D.free_wired_multiOpen_eq_of_beta_not_badP_q2 d hd hβ hbad T

/--
[free_wired_boxConnEvent_eq_of_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_wired_boxConnEvent_eq_of_not_badP_q2_eq
  {d N : ℕ}
  {p : ℝ}
  {x y : boxVerts d N}
-- given
  (hd : 1 ≤ d)
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hbad : p ∉ FK.fwa_badP d) :
-- imply
  (FK.freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d N x y) = (FK.wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d N x y) := by
-- proof
  apply StatMech.Exact3D.free_wired_boxConnEvent_eq_of_not_badP_q2 d N hd hN hp hp1 hbad x y

/--
[free_wired_boxConnEvent_eq_of_beta_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_wired_boxConnEvent_eq_of_beta_not_badP_q2_eq
  {d N : ℕ}
  {β : ℝ}
  {x y : boxVerts d N}
-- given
  (hd : 1 ≤ d)
  (hN : 1 ≤ N)
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP d) :
-- imply
  (FK.freeInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d N x y) = (FK.wiredInfiniteVolume d (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d N x y) := by
-- proof
  apply StatMech.Exact3D.free_wired_boxConnEvent_eq_of_beta_not_badP_q2 d N hd hN hβ hbad x y

/--
[freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hn : 1 ≤ n) :
-- imply
  freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n = wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n := by
-- proof
  apply StatMech.Exact3D.freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2 hβ hbad hn

/--
[wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hn : 1 ≤ n) :
-- imply
  wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n = freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n := by
-- proof
  apply StatMech.Exact3D.wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2 hβ hbad hn

/--
[eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  ∀ᶠ n in atTop, freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n = wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n := by
-- proof
  apply StatMech.Exact3D.eventually_freeInfiniteVolumeXAxisConnection_eq_wired_of_beta_not_badP_q2 hβ hbad

/--
[eventually_wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma eventually_wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  ∀ᶠ n in atTop, wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n = freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n := by
-- proof
  apply StatMech.Exact3D.eventually_wiredInfiniteVolumeXAxisConnection_eq_free_of_beta_not_badP_q2 hβ hbad

/--
[freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβ) :
-- imply
  FreeXAxisWiredQ2ConnectionAgrees β hβ := by
-- proof
  apply StatMech.Exact3D.freeXAxisWiredQ2ConnectionAgrees_of_free_not_badP hβ hbad hfree

/--
[freeXAxisQ2ConnectionAgrees_of_wired_not_badP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma freeXAxisQ2ConnectionAgrees_of_wired_not_badP_eq
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hwired : FreeXAxisWiredQ2ConnectionAgrees β hβ) :
-- imply
  FreeXAxisQ2ConnectionAgrees β hβ := by
-- proof
  apply StatMech.Exact3D.freeXAxisQ2ConnectionAgrees_of_wired_not_badP hβ hbad hwired

/--
[plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree_eq
  {β : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos) :
-- imply
  PlusXAxisWiredQ2ConnectionAgrees β hβpos := by
-- proof
  apply StatMech.Exact3D.plusXAxisWiredQ2ConnectionAgrees_of_free_not_badP_and_plusFree hβpos hβc hagree hbad hfree

/--
[fkXAxisConnectionExactExponentialDecay_freeInfiniteVolumeQ2_iff_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkXAxisConnectionExactExponentialDecay_freeInfiniteVolumeQ2_iff_wired_eq
  {β A m : ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔ FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionExactExponentialDecay_freeInfiniteVolumeQ2_iff_wired hβ hbad

/--
[fkXAxisConnectionExactExponentialDecay_wiredInfiniteVolumeQ2_iff_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkXAxisConnectionExactExponentialDecay_wiredInfiniteVolumeQ2_iff_free_eq
  {β A m : ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔ FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionExactExponentialDecay_wiredInfiniteVolumeQ2_iff_free hβ hbad

/--
[fkXAxisConnectionSubexponentialPrefactorDecay_freeInfiniteVolumeQ2_iff_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkXAxisConnectionSubexponentialPrefactorDecay_freeInfiniteVolumeQ2_iff_wired_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔ FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionSubexponentialPrefactorDecay_freeInfiniteVolumeQ2_iff_wired hβ hbad

/--
[fkXAxisConnectionSubexponentialPrefactorDecay_wiredInfiniteVolumeQ2_iff_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkXAxisConnectionSubexponentialPrefactorDecay_wiredInfiniteVolumeQ2_iff_free_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m ↔ FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) A m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionSubexponentialPrefactorDecay_wiredInfiniteVolumeQ2_iff_free hβ hbad

/--
[fkXAxisConnectionTwoSidedSubexponentialBounds_freeInfiniteVolumeQ2_iff_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkXAxisConnectionTwoSidedSubexponentialBounds_freeInfiniteVolumeQ2_iff_wired_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m ↔ FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionTwoSidedSubexponentialBounds_freeInfiniteVolumeQ2_iff_wired hβ hbad

/--
[fkXAxisConnectionTwoSidedSubexponentialBounds_wiredInfiniteVolumeQ2_iff_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma fkXAxisConnectionTwoSidedSubexponentialBounds_wiredInfiniteVolumeQ2_iff_free_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβ : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3) :
-- imply
  FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m ↔ FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo Ahi m := by
-- proof
  apply StatMech.Exact3D.fkXAxisConnectionTwoSidedSubexponentialBounds_wiredInfiniteVolumeQ2_iff_free hβ hbad

/--
[free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential hβpos hA hfree hconn

/--
[plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential hβpos hβc hA hagree hfree hconn

/--
[free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor hβpos hfree hconn

/--
[plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor hβpos hβc hagree hfree hconn

/--
[free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided hβpos hfree hconn

/--
[plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided hβpos hβc hagree hfree hconn

/--
[free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential hβpos hA hbad hfree hconn

/--
[plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential hβpos hβc hA hagree hbad hfree hconn

/--
[free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor hβpos hbad hfree hconn

/--
[plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor hβpos hβc hagree hbad hfree hconn

/--
[free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided hβpos hbad hfree hconn

/--
[plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided hβpos hβc hagree hbad hfree hconn

/--
[free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hm : 0 < m)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential hβpos hA hm hfree hconn

/--
[plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hm : 0 < m)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_exactExponential hβpos hβc hA hm hagree hfree hconn

/--
[free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hm : 0 < m)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor hβpos hm hfree hconn

/--
[plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hm : 0 < m)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_subexponentialPrefactor hβpos hβc hm hagree hfree hconn

/--
[free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hm : 0 < m)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided hβpos hm hfree hconn

/--
[plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hm : 0 < m)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_twoSided hβpos hβc hm hagree hfree hconn

/--
[free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hm : 0 < m)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential hβpos hA hm hbad hfree hconn

/--
[free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hm : 0 < m)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor hβpos hm hbad hfree hconn

/--
[free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hm : 0 < m)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSided hβpos hm hbad hfree hconn

/--
[plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential_eq
  {β A m : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hm : 0 < m)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionExactExponentialDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_exactExponential hβpos hβc hA hm hagree hbad hfree hconn

/--
[plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor_eq
  {β m : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hm : 0 < m)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionSubexponentialPrefactorDecay (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) A m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_subexponentialPrefactor hβpos hβc hm hagree hbad hfree hconn

/--
[plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSidedSubexponentialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSidedSubexponentialBounds_eq
  {β m : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hm : 0 < m)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds (wiredInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo Ahi m) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_wiredInfiniteVolumeQ2_twoSidedSubexponentialBounds hβpos hβc hm hagree hbad hfree hconn

/--
[free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential hβpos hA hfree hexact

/--
[plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential hβpos hβc hA hagree hfree hexact

/--
[free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hmass : 0 < mass)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential hβpos hA hmass hfree hexact

/--
[plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hmass : 0 < mass)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential hβpos hβc hA hmass hagree hfree hexact

/--
[free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor hβpos hfree hsubexp

/--
[plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor hβpos hβc hagree hfree hsubexp

/--
[free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hmass : 0 < mass)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor hβpos hmass hfree hsubexp

/--
[plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hmass : 0 < mass)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor hβpos hβc hmass hagree hfree hsubexp

/--
[free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential hβpos hA hbad hfree hexact

/--
[plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential hβpos hβc hA hagree hbad hfree hexact

/--
[free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hA : 0 < A)
  (hmass : 0 < mass)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential hβpos hA hmass hbad hfree hexact

/--
[plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential_eq
  {β A mass : ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hA : 0 < A)
  (hmass : 0 < mass)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hexact : WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential hβpos hβc hA hmass hagree hbad hfree hexact

/--
[free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor hβpos hbad hfree hsubexp

/--
[plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor hβpos hβc hagree hbad hfree hsubexp

/--
[free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hmass : 0 < mass)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor hβpos hmass hbad hfree hsubexp

/--
[plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor_eq
  {β mass : ℝ}
  {A : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hmass : 0 < mass)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hsubexp : WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor hβpos hβc hmass hagree hbad hfree hsubexp

/--
[free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided hβpos hfree hbounds

/--
[plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided hβpos hβc hagree hfree hbounds

/--
[free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hmass : 0 < mass)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided hβpos hmass hfree hbounds

/--
[plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hmass : 0 < mass)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided hβpos hβc hmass hagree hfree hbounds

/--
[free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided hβpos hbad hfree hbounds

/--
[plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass := by
-- proof
  apply StatMech.Exact3D.plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided hβpos hβc hagree hbad hfree hbounds

/--
[free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hmass : 0 < mass)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.free_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided hβpos hmass hbad hfree hbounds

/--
[plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hmass : 0 < mass)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hbounds : WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided hβpos hβc hmass hagree hbad hfree hbounds

/--
[plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSidedSubexpBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSidedSubexpBounds_eq
  {β mass : ℝ}
  {Alo Ahi : ℕ → ℝ}
-- given
  (hβpos : 0 < β)
  (hβc : β < Ising.betaC 3)
  (hmass : 0 < mass)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : IsingFK.pOfBeta β ∉ FK.fwa_badP 3)
  (hfree : FreeXAxisQ2ConnectionAgrees β hβpos)
  (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
  (hlo_log : Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) atTop (nhds 0))
  (hhi_log : Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop (nhds 0))
  (hlo : ∀ᶠ n in atTop, ∀ᶠ M in atTop, Alo n * Real.exp (-(mass * (n : ℝ))) ≤ (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)))
  (hhi : ∀ᶠ n in atTop, ∀ᶠ M in atTop, (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (boxConnEvent 3 n (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)) ≤ Ahi n * Real.exp (-(mass * (n : ℝ)))) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay mass⁻¹ := by
-- proof
  apply StatMech.Exact3D.plus_hasCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSidedSubexpBounds hβpos hβc hmass hagree hbad hfree hlo_pos hhi_pos hlo_log hhi_log hlo hhi


-- created on 2026-10-23
