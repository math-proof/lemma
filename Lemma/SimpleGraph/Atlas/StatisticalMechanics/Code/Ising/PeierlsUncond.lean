import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part11
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[flipOnSet_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma flipOnSet_apply_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {x : Site d} :
-- imply
  flipOnSet K σ x = if x ∈ K then !(σ x) else σ x := by
-- proof
  apply StatMech.Ising.flipOnSet_apply K σ x

/--
[flipOnSet_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma flipOnSet_mem_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hx : x ∈ K) :
-- imply
  flipOnSet K σ x = !(σ x) := by
-- proof
  apply StatMech.Ising.flipOnSet_mem K σ hx

/--
[flipOnSet_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma flipOnSet_not_mem_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hx : x ∉ K) :
-- imply
  flipOnSet K σ x = σ x := by
-- proof
  apply StatMech.Ising.flipOnSet_not_mem K σ hx

/--
[spin_flipOnSet_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma spin_flipOnSet_mem_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hx : x ∈ K) :
-- imply
  spin (flipOnSet K σ) x = - spin σ x := by
-- proof
  apply StatMech.Ising.spin_flipOnSet_mem K σ hx

/--
[spin_flipOnSet_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma spin_flipOnSet_not_mem_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hx : x ∉ K) :
-- imply
  spin (flipOnSet K σ) x = spin σ x := by
-- proof
  apply StatMech.Ising.spin_flipOnSet_not_mem K σ hx

/--
[crosses_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma crosses_mk_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d} :
-- imply
  crosses K s(x, y) ↔ (x ∈ K ↔ y ∉ K) := by
-- proof
  apply StatMech.Ising.crosses_mk K x y

/--
[crossEdgeBond_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma crossEdgeBond_mk_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {x y : Site d} :
-- imply
  crossEdgeBond K σ s(x, y) = if (x ∈ K ↔ y ∉ K) then bond σ s(x, y) else 0 := by
-- proof
  apply StatMech.Ising.crossEdgeBond_mk K σ x y

/--
[crossEdgeBond_of_not_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma crossEdgeBond_of_not_crosses_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {e : Sym2 (Site d)}
-- given
  (he : ¬ crosses K e) :
-- imply
  crossEdgeBond K σ e = 0 := by
-- proof
  apply StatMech.Ising.crossEdgeBond_of_not_crosses K σ he

/--
[crossEdgeBond_of_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma crossEdgeBond_of_crosses_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {e : Sym2 (Site d)}
-- given
  (he : crosses K e) :
-- imply
  crossEdgeBond K σ e = bond σ e := by
-- proof
  apply StatMech.Ising.crossEdgeBond_of_crosses K σ he

/--
[bond_flipOnSet_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma bond_flipOnSet_diff_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {x y : Site d} :
-- imply
  bond (flipOnSet K σ) s(x, y) - bond σ s(x, y) = -2 * crossEdgeBond K σ s(x, y) := by
-- proof
  apply StatMech.Ising.bond_flipOnSet_diff K σ x y

/--
[bond_flipOnSet_diff_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma bond_flipOnSet_diff_edge_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  bond (flipOnSet K σ) e - bond σ e = -2 * crossEdgeBond K σ e := by
-- proof
  apply StatMech.Ising.bond_flipOnSet_diff_edge K σ e

/--
[bondSum_flipOnSet_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma bondSum_flipOnSet_diff_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))} :
-- imply
  (∑ e ∈ B, bond (flipOnSet K σ) e) - (∑ e ∈ B, bond σ e) = -2 * ∑ e ∈ B, crossEdgeBond K σ e := by
-- proof
  apply StatMech.Ising.bondSum_flipOnSet_diff K σ B

/--
[sum_crossEdgeBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma sum_crossEdgeBond_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))} :
-- imply
  (∑ e ∈ B, crossEdgeBond K σ e) = ∑ e ∈ crossEdges K B, bond σ e := by
-- proof
  apply StatMech.Ising.sum_crossEdgeBond K σ B

/--
[sum_crossEdgeBond_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma sum_crossEdgeBond_event_eq
  {d : ℕ}
  {K : Set (Site d)}
  {σ : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : ContourEvent K B σ) :
-- imply
  (∑ e ∈ B, crossEdgeBond K σ e) = - (contourLen K B : ℝ) := by
-- proof
  apply StatMech.Ising.sum_crossEdgeBond_event K σ B h

/--
[flipInteriorOn_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma flipInteriorOn_involutive_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  flipInteriorOn K (flipInteriorOn K τ) = τ := by
-- proof
  apply StatMech.Ising.flipInteriorOn_involutive K τ

/--
[flipInteriorOnEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma flipInteriorOnEquiv_apply_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  flipInteriorOnEquiv K τ = flipInteriorOn K τ := by
-- proof
  apply StatMech.Ising.flipInteriorOnEquiv_apply K τ

/--
[glue_flipInteriorOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma glue_flipInteriorOn_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
  {η : ConfigSpace (Site d)}
-- given
  (hK : K ⊆ box d n)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  glue η (flipInteriorOn K τ) = flipOnSet K (glue η τ) := by
-- proof
  apply StatMech.Ising.glue_flipInteriorOn K hK η τ

/--
[fvEnergy_flipInteriorOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma fvEnergy_flipInteriorOn_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
  {η : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
-- given
  (hK : K ⊆ box d n)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy η n B 0 (flipInteriorOn K τ) = fvEnergy η n B 0 τ + 2 * ∑ e ∈ B, crossEdgeBond K (glue η τ) e := by
-- proof
  apply StatMech.Ising.fvEnergy_flipInteriorOn n K hK η B τ

/--
[fvWeight_flipInteriorOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma fvWeight_flipInteriorOn_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
  {η : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hK : K ⊆ box d n)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight η n B β 0 (flipInteriorOn K τ) = Real.exp (-β * (2 * ∑ e ∈ B, crossEdgeBond K (glue η τ) e)) * fvWeight η n B β 0 τ := by
-- proof
  apply StatMech.Ising.fvWeight_flipInteriorOn n K hK η B β τ

/--
[fvWeight_flipInteriorOn_eq_of_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma fvWeight_flipInteriorOn_eq_of_event_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
  {η : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hK : K ⊆ box d n)
  (τ : {x // x ∈ box d n} → Bool)
  (hev : ContourEvent K B (glue η τ)) :
-- imply
  fvWeight η n B β 0 τ = Real.exp (-(2 * β) * (contourLen K B : ℝ)) * fvWeight η n B β 0 (flipInteriorOn K τ) := by
-- proof
  apply StatMech.Ising.fvWeight_flipInteriorOn_eq_of_event n K hK η B β τ hev

/--
[probContour_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma probContour_nonneg_eq
  {d : ℕ}
  {K : Set (Site d)}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ} :
-- imply
  0 ≤ probContour K η n B β := by
-- proof
  apply StatMech.Ising.probContour_nonneg K η n B β

/--
[contour_energy_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma contour_energy_bound_eq
  {d : ℕ}
  {n : ℕ}
  {K : Set (Site d)}
  {η : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hK : K ⊆ box d n) :
-- imply
  probContour K η n B β ≤ Real.exp (-(2 * β) * (contourLen K B : ℝ)) := by
-- proof
  apply StatMech.Ising.contour_energy_bound n K hK η B β

/--
[mem_minusSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma mem_minusSet_eq
  {d : ℕ}
  {σ : ConfigSpace (Site d)}
  {x : Site d} :
-- imply
  x ∈ minusSet σ ↔ σ x = false := by
-- proof
  apply StatMech.Ising.mem_minusSet

/--
[origin_mem_minusCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma origin_mem_minusCluster_eq
  {d : ℕ}
  {σ : ConfigSpace (Site d)}
  {o : Site d} :
-- imply
  o ∈ minusCluster σ o := by
-- proof
  apply StatMech.Ising.origin_mem_minusCluster o

/--
[minusCluster_subset_minusSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma minusCluster_subset_minusSet_eq
  {d : ℕ}
  {σ : ConfigSpace (Site d)}
  {o : Site d}
-- given
  (ho : o ∈ minusSet σ) :
-- imply
  minusCluster σ o ⊆ minusSet σ := by
-- proof
  apply StatMech.Ising.minusCluster_subset_minusSet ho

/--
[minusCluster_cross_disagree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma minusCluster_cross_disagree_eq
  {d : ℕ}
  {σ : ConfigSpace (Site d)}
  {o : Site d}
  {x y : Site d}
-- given
  (ho : o ∈ minusSet σ)
  (hadj : (hypercubicLattice d).Adj x y)
  (hxy : x ∈ minusCluster σ o ↔ y ∉ minusCluster σ o) :
-- imply
  spin σ x * spin σ y = -1 := by
-- proof
  apply StatMech.Ising.minusCluster_cross_disagree ho hadj hxy

/--
[adj_of_mem_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma adj_of_mem_bondFinsetTouch_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d}
-- given
  (h : s(x, y) ∈ bondFinsetTouch d n) :
-- imply
  (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.Ising.adj_of_mem_bondFinsetTouch h

/--
[contourEvent_of_origin_minus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma contourEvent_of_origin_minus_eq
  {d : ℕ}
  {σ : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (ho : σ (origin d) = false) :
-- imply
  ContourEvent (minusCluster σ (origin d)) (bondFinsetTouch d n) σ := by
-- proof
  apply StatMech.Ising.contourEvent_of_origin_minus n ho

/--
[minusSet_glue_plus_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma minusSet_glue_plus_subset_box_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  minusSet (glue (plusField d) τ) ⊆ box d n := by
-- proof
  apply StatMech.Ising.minusSet_glue_plus_subset_box τ

/--
[minusCluster_glue_plus_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma minusCluster_glue_plus_subset_box_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (ho : glue (plusField d) τ (origin d) = false) :
-- imply
  minusCluster (glue (plusField d) τ) (origin d) ⊆ box d n := by
-- proof
  apply StatMech.Ising.minusCluster_glue_plus_subset_box τ ho

/--
[minusCluster_glue_plus_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma minusCluster_glue_plus_finite_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (ho : glue (plusField d) τ (origin d) = false) :
-- imply
  (minusCluster (glue (plusField d) τ) (origin d)).Finite := by
-- proof
  apply StatMech.Ising.minusCluster_glue_plus_finite τ ho

/--
[minusClusterFinset_mem_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma minusClusterFinset_mem_family_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (ho : glue (plusField d) τ (origin d) = false) :
-- imply
  minusClusterFinset τ ho ∈ clusterFamily (d := d) n := by
-- proof
  apply StatMech.Ising.minusClusterFinset_mem_family τ ho

/--
[minusClusterFinset_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma minusClusterFinset_coe_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (ho : glue (plusField d) τ (origin d) = false) :
-- imply
  ((minusClusterFinset τ ho : Finset (Site d)) : Set (Site d)) = minusCluster (glue (plusField d) τ) (origin d) := by
-- proof
  apply StatMech.Ising.minusClusterFinset_coe τ ho

/--
[clusterFamily_subset_boxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma clusterFamily_subset_boxFinset_eq
  {d : ℕ}
  {n : ℕ}
  {K : Finset (Site d)}
-- given
  (hK : K ∈ clusterFamily (d := d) n) :
-- imply
  K ⊆ boxFinset d n := by
-- proof
  apply StatMech.Ising.clusterFamily_subset_boxFinset hK

/--
[clusterFamily_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma clusterFamily_subset_box_eq
  {d : ℕ}
  {n : ℕ}
  {K : Finset (Site d)}
-- given
  (hK : K ∈ clusterFamily (d := d) n) :
-- imply
  (↑K : Set (Site d)) ⊆ box d n := by
-- proof
  apply StatMech.Ising.clusterFamily_subset_box hK

/--
[probOriginMinus_le_sum_probContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma probOriginMinus_le_sum_probContour_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 ≤ ∑ K ∈ clusterFamily (d := d) n, probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
-- proof
  apply StatMech.Ising.probOriginMinus_le_sum_probContour n β

/--
[probOriginMinus_le_sum_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma probOriginMinus_le_sum_exp_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 ≤ ∑ K ∈ clusterFamily (d := d) n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
-- proof
  apply StatMech.Ising.probOriginMinus_le_sum_exp n β

/--
[peierlsContourBound_of_contourCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma peierlsContourBound_of_contourCount_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hCount : ContourCountBound d n β) :
-- imply
  PeierlsContourBound d n β := by
-- proof
  apply StatMech.Ising.peierlsContourBound_of_contourCount n β hCount

/--
[peierls_long_range_order_of_contourCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean)
-/
@[path]
private lemma peierls_long_range_order_of_contourCount_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hCount : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → ContourCountBound d n β) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.peierls_long_range_order_of_contourCount hd hCount


-- created on 2026-10-23
