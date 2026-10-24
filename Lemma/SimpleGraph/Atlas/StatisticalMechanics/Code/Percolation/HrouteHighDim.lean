import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.HrouteHighDim
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[hrHD_rayPt_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_rayPt_self_eq
  {d : ℕ}
  {j : Fin d}
  {t : ℤ} :
-- imply
  hrHD_rayPt j t j = t := by
-- proof
  apply StatMech.Percolation.hrHD_rayPt_self j t

/--
[hrHD_rayPt_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_rayPt_of_ne_eq
  {d : ℕ}
  {j : Fin d}
  {t : ℤ}
  {i : Fin d}
-- given
  (h : i ≠ j) :
-- imply
  hrHD_rayPt j t i = 0 := by
-- proof
  apply StatMech.Percolation.hrHD_rayPt_of_ne j t h

/--
[hrHD_rayPt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_rayPt_zero_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  hrHD_rayPt j 0 = (0 : Site d) := by
-- proof
  apply StatMech.Percolation.hrHD_rayPt_zero j

/--
[hrHD_rayPt_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_rayPt_eq_zero_iff_eq
  {d : ℕ}
  {j : Fin d}
  {t : ℤ} :
-- imply
  hrHD_rayPt j t = (0 : Site d) ↔ t = 0 := by
-- proof
  apply StatMech.Percolation.hrHD_rayPt_eq_zero_iff j t

/--
[hrHD_adj_rayPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_adj_rayPt_eq
  {d : ℕ}
  {j : Fin d}
  {t : ℤ} :
-- imply
  (hypercubicLattice d).Adj (hrHD_rayPt j t) (hrHD_rayPt j (t + 1)) := by
-- proof
  apply StatMech.Percolation.hrHD_adj_rayPt j t

/--
[hrHD_adj_origin_rayPt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_adj_origin_rayPt_one_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  (hypercubicLattice d).Adj (0 : Site d) (hrHD_rayPt j 1) := by
-- proof
  apply StatMech.Percolation.hrHD_adj_origin_rayPt_one j

/--
[hrHD_rayPt_one_ne_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_rayPt_one_ne_of_ne_eq
  {d : ℕ}
  {i j : Fin d}
-- given
  (h : i ≠ j) :
-- imply
  (hrHD_rayPt i 1 : Site d) ≠ hrHD_rayPt j 1 := by
-- proof
  apply StatMech.Percolation.hrHD_rayPt_one_ne_of_ne h

/--
[hrHD_rayPt_disjoint_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_rayPt_disjoint_of_ne_eq
  {d : ℕ}
  {i j : Fin d}
  {s t : ℤ}
-- given
  (h : i ≠ j)
  (hs : s ≠ 0) :
-- imply
  (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
-- proof
  apply StatMech.Percolation.hrHD_rayPt_disjoint_of_ne h hs

/--
[hrHD_mem_corridorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_mem_corridorEdges_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {t : ℕ}
-- given
  (ht : t < L) :
-- imply
  s(hrHD_rayPt j (t : ℤ), hrHD_rayPt j ((t : ℤ) + 1)) ∈ hrHD_corridorEdges j L := by
-- proof
  apply StatMech.Percolation.hrHD_mem_corridorEdges ht

/--
[hrHD_origin_notMem_rayEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_origin_notMem_rayEdge_eq
  {d : ℕ}
  {j : Fin d}
  {s : ℤ}
-- given
  (hs : 1 ≤ s) :
-- imply
  (0 : Site d) ∉ s(hrHD_rayPt j s, hrHD_rayPt j (s + 1)) := by
-- proof
  apply StatMech.Percolation.hrHD_origin_notMem_rayEdge j s hs

/--
[hrHD_corridor_step_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_corridor_step_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {s : ℕ}
-- given
  (h0 : 1 ≤ s)
  (hsL : s < L) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) := by
-- proof
  apply StatMech.Percolation.hrHD_corridor_step_open ω j L s h0 hsL

/--
[hrHD_corridor_connected_one_to_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_corridor_connected_one_to_L_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) := by
-- proof
  apply StatMech.Percolation.hrHD_corridor_connected_one_to_L ω j L hL

/--
[hrHD_precursor_of_removeSite_conditions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_precursor_of_removeSite_conditions_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite)
  (hdist : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧ cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃ := by
-- proof
  apply StatMech.Percolation.hrHD_precursor_of_removeSite_conditions ω a₁ a₂ a₃ hne hadj hinf hdist

/--
[hrHD_measurableSet_neighborTrifPrecursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_measurableSet_neighborTrifPrecursor_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d} :
-- imply
  MeasurableSet (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Percolation.hrHD_measurableSet_neighborTrifPrecursor a₁ a₂ a₃

/--
[hrHD_threeMeetBox_subset_iUnion_routePre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_threeMeetBox_subset_iUnion_routePre_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hrt : hrHD_DisjointRouting d n) :
-- imply
  threeMeetBox d n ⊆ ⋃ p : hrHD_RouteIdx d, hrHD_routePre p := by
-- proof
  apply StatMech.Percolation.hrHD_threeMeetBox_subset_iUnion_routePre hrt

/--
[hrHD_route_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_route_step_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hrt : hrHD_DisjointRouting d n)
  (hpos : 0 < μ (threeMeetBox d n)) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Percolation.hrHD_route_step μ hfe n hrt hpos

/--
[hrHD_route_of_routing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_route_of_routing_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Percolation.hrHD_route_of_routing μ hfe hrt

/--
[hrHD_exists_three_independent_axes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_exists_three_independent_axes_eq
  {d : ℕ}
-- given
  (hd : 3 ≤ d) :
-- imply
  ∃ j₁ j₂ j₃ : Fin d, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ := by
-- proof
  apply StatMech.Percolation.hrHD_exists_three_independent_axes hd

/--
[hrHD_axis_corridor_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_axis_corridor_branches_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L : ℕ}
-- given
  (h12 : j₁ ≠ j₂)
  (h13 : j₁ ≠ j₃)
  (h23 : j₂ ≠ j₃)
  (hL : 1 ≤ L) :
-- imply
  (hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₂ 1 ∧ hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₃ 1 ∧ hrHD_rayPt j₂ 1 ≠ hrHD_rayPt j₃ 1) ∧ ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧ (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₂ t) ∧ (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₃ t) ∧ (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₂ s ≠ hrHD_rayPt j₃ t) ∧ (Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ L) ω)) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₁ (L : ℤ)) ∧ Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₂ L) ω)) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₂ (L : ℤ)) ∧ Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₃ L) ω)) (hrHD_rayPt j₃ 1) (hrHD_rayPt j₃ (L : ℤ))) := by
-- proof
  apply StatMech.Percolation.hrHD_axis_corridor_branches ω h12 h13 h23 L hL

/--
[hrHD_burton_keane_uniqueness_dim_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean)
-/
@[path]
private lemma hrHD_burton_keane_uniqueness_dim_ge_three_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (hd : 3 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  (∃ j₁ j₂ j₃ : Fin d, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧ (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.hrHD_burton_keane_uniqueness_dim_ge_three hd μ herg hfe bdry hbound hvol hdens hrt


-- created on 2026-10-23
