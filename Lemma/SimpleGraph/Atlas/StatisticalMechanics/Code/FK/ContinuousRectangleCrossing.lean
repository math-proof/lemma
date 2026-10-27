import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
open Set SimpleGraph Topology StatMech StatMech.ContinuousRectangleCrossing


/--
[site_eq_vec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma site_eq_vec_eq
  {z : Site 2} :
-- imply
  z = ![z 0, z 1] := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.site_eq_vec z

/--
[gridConnector_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridConnector_mem_support_eq
  {x y z : Site 2} :
-- imply
  z ∈ (gridConnector x y).support ↔ (∃ t : ℤ, t ∈ Set.uIcc (x 0) (y 0) ∧ z = ![t, x 1]) ∨ (∃ t : ℤ, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![y 0, t]) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridConnector_mem_support x y z

/--
[gridWalk_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridWalk_zero_eq
  {g : ℕ → Site 2} :
-- imply
  gridWalk g 0 = Walk.nil := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridWalk_zero g

/--
[gridWalk_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridWalk_succ_eq
  {g : ℕ → Site 2}
  {n : ℕ} :
-- imply
  gridWalk g (n + 1) = (gridWalk g n).append (gridConnector (g n) (g (n + 1))) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridWalk_succ g n

/--
[gridWalk_mem_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridWalk_mem_support_cases_eq
  {g : ℕ → Site 2}
  {n : ℕ}
  {z : Site 2}
-- given
  (hz : z ∈ (gridWalk g n).support) :
-- imply
  z = g 0 ∨ ∃ k < n, z ∈ (gridConnector (g k) (g (k + 1))).support := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridWalk_mem_support_cases g n z hz

/--
[sampleTime_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampleTime_zero_eq
  {N : ℕ}
-- given
  (hN : 0 < N) :
-- imply
  sampleTime N 0 (Nat.zero_le N) hN = 0 := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampleTime_zero N hN

/--
[sampleTime_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampleTime_self_eq
  {N : ℕ}
-- given
  (hN : 0 < N) :
-- imply
  sampleTime N N (le_refl N) hN = 1 := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampleTime_self N hN

/--
[dist_sampleTime_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma dist_sampleTime_succ_eq
  {N k : ℕ}
-- given
  (hk : k < N)
  (hN : 0 < N) :
-- imply
  dist (sampleTime N k hk.le hN) (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN) = 1 / (N : ℝ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.dist_sampleTime_succ N k hk hN

/--
[gridFloor_coord_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridFloor_coord_nonneg_eq
  {n : ℕ}
  {p : Fin 2 → ℝ}
  {i : Fin 2}
-- given
  (hp : InUnitSquare p) :
-- imply
  0 ≤ gridFloor n p i := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridFloor_coord_nonneg hp i

/--
[gridFloor_coord_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridFloor_coord_le_eq
  {n : ℕ}
  {p : Fin 2 → ℝ}
  {i : Fin 2}
-- given
  (hp : InUnitSquare p) :
-- imply
  gridFloor n p i ≤ (n : ℤ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridFloor_coord_le hp i

/--
[gridFloor_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridFloor_error_eq
  {n : ℕ}
  {p : Fin 2 → ℝ}
  {i : Fin 2}
-- given
  (hn : 0 < n) :
-- imply
  |gridEmbed n (gridFloor n p) i - p i| < 1 / (n : ℝ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridFloor_error hn p i

/--
[abs_lt_of_mem_uIcc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma abs_lt_of_mem_uIcc_eq
  {a b t x e : ℝ}
-- given
  (ht : t ∈ Set.uIcc a b)
  (ha : |a - x| < e)
  (hb : |b - x| < e) :
-- imply
  |t - x| < e := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.abs_lt_of_mem_uIcc ht ha hb

/--
[div_mem_uIcc_of_int_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma div_mem_uIcc_of_int_mem_eq
  {n : ℕ}
  {a b t : ℤ}
-- given
  (hn : 0 < n)
  (ht : t ∈ Set.uIcc a b) :
-- imply
  (t : ℝ) / n ∈ Set.uIcc ((a : ℝ) / n) ((b : ℝ) / n) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.div_mem_uIcc_of_int_mem hn ht

/--
[gridFloor_other_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridFloor_other_error_eq
  {n : ℕ}
  {p q : Fin 2 → ℝ}
  {i : Fin 2}
-- given
  (hn : 0 < n)
  (hpq : |p i - q i| < 1 / (n : ℝ)) :
-- imply
  |gridEmbed n (gridFloor n q) i - p i| < 3 / (n : ℝ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridFloor_other_error hn hpq

/--
[gridConnector_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridConnector_near_eq
  {n : ℕ}
  {p q : Fin 2 → ℝ}
  {z : Site 2}
-- given
  (hn : 0 < n)
  (hpq : dist p q < 1 / (n : ℝ))
  (hz : z ∈ (gridConnector (gridFloor n p) (gridFloor n q)).support) :
-- imply
  dist (gridEmbed n z) p < 3 / (n : ℝ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridConnector_near hn hpq hz

/--
[gridFloor_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridFloor_near_eq
  {n : ℕ}
  {p : Fin 2 → ℝ}
-- given
  (hn : 0 < n) :
-- imply
  dist (gridEmbed n (gridFloor n p)) p < 3 / (n : ℝ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridFloor_near hn p

/--
[coord_bounds_of_mem_uIcc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma coord_bounds_of_mem_uIcc_eq
  {a b t lo hi : ℤ}
-- given
  (ht : t ∈ Set.uIcc a b)
  (ha0 : lo ≤ a)
  (ha1 : a ≤ hi)
  (hb0 : lo ≤ b)
  (hb1 : b ≤ hi) :
-- imply
  lo ≤ t ∧ t ≤ hi := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.coord_bounds_of_mem_uIcc ht ha0 ha1 hb0 hb1

/--
[gridConnector_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridConnector_mem_rect_eq
  {n : ℕ}
  {x y z : Site 2}
-- given
  (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ))
  (hy : y ∈ rect 0 (n : ℤ) 0 (n : ℤ))
  (hz : z ∈ (gridConnector x y).support) :
-- imply
  z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridConnector_mem_rect hx hy hz

/--
[gridWalk_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridWalk_mem_rect_eq
  {n N : ℕ}
  {g : ℕ → Site 2}
  {z : Site 2}
-- given
  (hg : ∀ k ≤ N, g k ∈ rect 0 (n : ℤ) 0 (n : ℤ))
  (hz : z ∈ (gridWalk g N).support) :
-- imply
  z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridWalk_mem_rect hg hz

/--
[sampledGrid_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampledGrid_eq_eq
  {p q : Fin 2 → ℝ}
  {n N : ℕ}
  {gamma : Path p q}
  {k : ℕ}
-- given
  (hN : 0 < N)
  (hk : k ≤ N) :
-- imply
  sampledGrid n N hN gamma k = gridFloor n (gamma (sampleTime N k hk hN)) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampledGrid_eq n N hN gamma hk

/--
[sampledGrid_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampledGrid_zero_eq
  {p q : Fin 2 → ℝ}
  {n N : ℕ}
  {gamma : Path p q}
-- given
  (hN : 0 < N) :
-- imply
  sampledGrid n N hN gamma 0 = gridFloor n p := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampledGrid_zero n N hN gamma

/--
[sampledGrid_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampledGrid_self_eq
  {p q : Fin 2 → ℝ}
  {n N : ℕ}
  {gamma : Path p q}
-- given
  (hN : 0 < N) :
-- imply
  sampledGrid n N hN gamma N = gridFloor n q := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampledGrid_self n N hN gamma

/--
[exists_fine_sampling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma exists_fine_sampling_eq
  {p q : Fin 2 → ℝ}
  {gamma : Path p q}
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∃ N : ℕ, ∃ hN : 0 < N, ∀ (k : ℕ) (hk : k < N), dist (gamma (sampleTime N k hk.le hN)) (gamma (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN)) < 1 / (n : ℝ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.exists_fine_sampling gamma hn

/--
[sampledGrid_walk_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampledGrid_walk_near_eq
  {p q : Fin 2 → ℝ}
  {gamma : Path p q}
  {n N : ℕ}
  {z : Site 2}
-- given
  (hn : 0 < n)
  (hN : 0 < N)
  (hfine : ∀ (k : ℕ) (hk : k < N), dist (gamma (sampleTime N k hk.le hN)) (gamma (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN)) < 1 / (n : ℝ))
  (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
-- imply
  ∃ t : unitInterval, dist (gridEmbed n z) (gamma t) < 3 / (n : ℝ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampledGrid_walk_near gamma hn hN hfine hz

/--
[sampledGrid_walk_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampledGrid_walk_mem_rect_eq
  {p q : Fin 2 → ℝ}
  {gamma : Path p q}
  {n N : ℕ}
  {z : Site 2}
-- given
  (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
  (hN : 0 < N)
  (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
-- imply
  z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampledGrid_walk_mem_rect gamma hgamma hN hz

/--
[gridFloor_coord_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridFloor_coord_eq_zero_eq
  {n : ℕ}
  {p : Fin 2 → ℝ}
  {i : Fin 2}
-- given
  (h : p i = 0) :
-- imply
  gridFloor n p i = 0 := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridFloor_coord_eq_zero h

/--
[gridFloor_coord_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma gridFloor_coord_eq_nat_eq
  {n : ℕ}
  {p : Fin 2 → ℝ}
  {i : Fin 2}
-- given
  (h : p i = 1) :
-- imply
  gridFloor n p i = (n : ℤ) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.gridFloor_coord_eq_nat h

/--
[sampled_grid_walks_intersect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma sampled_grid_walks_intersect_eq
  {hl hr vb vt : Fin 2 → ℝ}
  {gamma : Path hl hr}
  {eta : Path vb vt}
  {n NH NV : ℕ}
-- given
  (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
  (heta : Set.range eta ⊆ {x | InUnitSquare x})
  (hl0 : hl 0 = 0)
  (hr0 : hr 0 = 1)
  (vb1 : vb 1 = 0)
  (vt1 : vt 1 = 1)
  (hn : 0 < n)
  (hNH : 0 < NH)
  (hNV : 0 < NV) :
-- imply
  ∃ z : Site 2, z ∈ (gridWalk (sampledGrid n NH hNH gamma) NH).support ∧ z ∈ (gridWalk (sampledGrid n NV hNV eta) NV).support := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.sampled_grid_walks_intersect gamma eta hgamma heta hl0 hr0 vb1 vt1 hn hNH hNV

/--
[unitSquare_paths_intersect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma unitSquare_paths_intersect_eq
  {hl hr vb vt : Fin 2 → ℝ}
  {gamma : Path hl hr}
  {eta : Path vb vt}
-- given
  (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
  (heta : Set.range eta ⊆ {x | InUnitSquare x})
  (hl0 : hl 0 = 0)
  (hr0 : hr 0 = 1)
  (vb1 : vb 1 = 0)
  (vt1 : vt 1 = 1) :
-- imply
  ∃ t s : unitInterval, gamma t = eta s := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.unitSquare_paths_intersect gamma eta hgamma heta hl0 hr0 vb1 vt1

/--
[continuous_normalizeRectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma continuous_normalizeRectangle_eq
  {a b c d : ℝ} :
-- imply
  Continuous (normalizeRectangle a b c d) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.continuous_normalizeRectangle a b c d

/--
[normalizeRectangle_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma normalizeRectangle_injective_eq
  {a b c d : ℝ}
-- given
  (hab : a < b)
  (hcd : c < d) :
-- imply
  Function.Injective (normalizeRectangle a b c d) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.normalizeRectangle_injective hab hcd

/--
[normalizeRectangle_mem_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma normalizeRectangle_mem_unitSquare_eq
  {a b c d : ℝ}
  {p : Fin 2 → ℝ}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hp : InRectangle a b c d p) :
-- imply
  InUnitSquare (normalizeRectangle a b c d p) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.normalizeRectangle_mem_unitSquare hab hcd hp

/--
[rectangle_paths_intersect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma rectangle_paths_intersect_eq
  {a b c d : ℝ}
  {hl hr vb vt : Fin 2 → ℝ}
  {gamma : Path hl hr}
  {eta : Path vb vt}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hgamma : Set.range gamma ⊆ {x | InRectangle a b c d x})
  (heta : Set.range eta ⊆ {x | InRectangle a b c d x})
  (hl0 : hl 0 = a)
  (hr0 : hr 0 = b)
  (vb1 : vb 1 = c)
  (vt1 : vt 1 = d) :
-- imply
  ∃ t s : unitInterval, gamma t = eta s := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.rectangle_paths_intersect hab hcd gamma eta hgamma heta hl0 hr0 vb1 vt1

/--
[clampCoord_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma clampCoord_bounds_eq
  {a b x : ℝ}
-- given
  (hab : a ≤ b) :
-- imply
  a ≤ clampCoord a b x ∧ clampCoord a b x ≤ b := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.clampCoord_bounds hab

/--
[clampCoord_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma clampCoord_of_mem_eq
  {a b x : ℝ}
-- given
  (hax : a ≤ x)
  (hxb : x ≤ b) :
-- imply
  clampCoord a b x = x := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.clampCoord_of_mem hax hxb

/--
[clampCoord_of_le_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma clampCoord_of_le_left_eq
  {a b x : ℝ}
-- given
  (hab : a ≤ b)
  (hx : x ≤ a) :
-- imply
  clampCoord a b x = a := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.clampCoord_of_le_left hab hx

/--
[clampCoord_of_right_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma clampCoord_of_right_le_eq
  {a b x : ℝ}
-- given
  (hab : a ≤ b)
  (hx : b ≤ x) :
-- imply
  clampCoord a b x = b := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.clampCoord_of_right_le hab hx

/--
[eq_of_clampCoord_eq_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma eq_of_clampCoord_eq_interior_eq
  {a b x y : ℝ}
-- given
  (hab : a < b)
  (hay : a < y)
  (hyb : y < b)
  (h : clampCoord a b x = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.eq_of_clampCoord_eq_interior hab hay hyb h

/--
[continuous_clampX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma continuous_clampX_eq
  {a b : ℝ} :
-- imply
  Continuous (clampX a b) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.continuous_clampX a b

/--
[continuous_clampY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma continuous_clampY_eq
  {c d : ℝ} :
-- imply
  Continuous (clampY c d) := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.continuous_clampY c d

/--
[strip_paths_intersect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean)
-/
@[path]
private lemma strip_paths_intersect_eq
  {a b c d : ℝ}
  {hl hr vb vt : Fin 2 → ℝ}
  {gamma : Path hl hr}
  {eta : Path vb vt}
-- given
  (hab : a < b)
  (hcd : c < d)
  (hl0 : hl 0 < a)
  (hr0 : b < hr 0)
  (vb1 : vb 1 < c)
  (vt1 : d < vt 1)
  (hgammaY : ∀ t : unitInterval, c < gamma t 1 ∧ gamma t 1 < d)
  (hetaX : ∀ t : unitInterval, a < eta t 0 ∧ eta t 0 < b) :
-- imply
  ∃ t s : unitInterval, gamma t = eta s := by
-- proof
  apply StatMech.ContinuousRectangleCrossing.strip_paths_intersect hab hcd gamma eta hl0 hr0 vb1 vt1 hgammaY hetaX


-- created on 2026-10-23
