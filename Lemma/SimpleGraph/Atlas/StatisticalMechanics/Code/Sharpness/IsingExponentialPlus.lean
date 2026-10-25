import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.IsingExponentialPlus.Part3
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech StatMech.Sharpness


/--
[ae_spin_eq_of_plusCorr_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma ae_spin_eq_of_plusCorr_eq_one_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hxy : plusCorr d beta x y = 1) :
-- imply
  ∀ᵐ omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))), spin omega x = spin omega y := by
-- proof
  apply StatMech.Sharpness.ae_spin_eq_of_plusCorr_eq_one beta x y hxy

/--
[site_nsmul_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma site_nsmul_injective_eq
  {d : ℕ}
  {x : Site d}
-- given
  (hx : x ≠ 0) :
-- imply
  Function.Injective (fun n : ℕ => n • x) := by
-- proof
  apply StatMech.Sharpness.site_nsmul_injective hx

/--
[plusCorr_eq_one_multiples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorr_eq_one_multiples_eq
  {d : ℕ}
  {beta : ℝ}
  {x : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hxone : plusCorr d beta (origin d) x = 1) :
-- imply
  ∀ n : ℕ, plusCorr d beta (origin d) (n • x) = 1 := by
-- proof
  apply StatMech.Sharpness.plusCorr_eq_one_multiples beta hbeta hxone

/--
[plusCorr_lt_one_of_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorr_lt_one_of_summable_eq
  {d : ℕ}
  {beta : ℝ}
  {x : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hsum : Summable (plusCorr d beta (origin d)))
  (hx : x ≠ origin d) :
-- imply
  plusCorr d beta (origin d) x < 1 := by
-- proof
  apply StatMech.Sharpness.plusCorr_lt_one_of_summable beta hbeta hsum hx

/--
[l1dist_origin_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma l1dist_origin_sub_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  l1dist d (origin d) (x - y) = l1dist d y x := by
-- proof
  apply StatMech.Sharpness.l1dist_origin_sub x y

/--
[l1dist_origin_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma l1dist_origin_eq_zero_iff_eq
  {d : ℕ}
  {z : Site d} :
-- imply
  l1dist d (origin d) z = 0 ↔ z = origin d := by
-- proof
  apply StatMech.Sharpness.l1dist_origin_eq_zero_iff z

/--
[mem_boxFinset_of_l1dist_origin_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma mem_boxFinset_of_l1dist_origin_le_eq
  {d : ℕ}
  {N : ℕ}
  {z : Site d}
-- given
  (h : l1dist d (origin d) z ≤ N) :
-- imply
  z ∈ Ising.boxFinset d N := by
-- proof
  apply StatMech.Sharpness.mem_boxFinset_of_l1dist_origin_le N z h

/--
[isingSimonRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma isingSimonRadius_pos_eq
  {d : ℕ}
  {T : Finset (Site d)} :
-- imply
  0 < isingSimonRadius d T := by
-- proof
  apply StatMech.Sharpness.isingSimonRadius_pos T

/--
[cut_lt_isingSimonRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma cut_lt_isingSimonRadius_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {x : Site d}
-- given
  (hx : x ∈ T) :
-- imply
  l1dist d (origin d) x < isingSimonRadius d T := by
-- proof
  apply StatMech.Sharpness.cut_lt_isingSimonRadius T hx

/--
[boundary_lt_isingSimonRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma boundary_lt_isingSimonRadius_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (he : e ∈ boundaryEdges d T) :
-- imply
  l1dist d (origin d) e.2 < isingSimonRadius d T := by
-- proof
  apply StatMech.Sharpness.boundary_lt_isingSimonRadius T he

/--
[plusCorrTailSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorrTailSet_nonempty_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  (plusCorrTailSet d beta n).Nonempty := by
-- proof
  apply StatMech.Sharpness.plusCorrTailSet_nonempty beta n

/--
[plusCorrTailSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorrTailSet_bddAbove_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  BddAbove (plusCorrTailSet d beta n) := by
-- proof
  apply StatMech.Sharpness.plusCorrTailSet_bddAbove beta n

/--
[plusCorr_le_tailSup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorr_le_tailSup_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ}
  {z : Site d}
-- given
  (hz : n ≤ l1dist d (origin d) z) :
-- imply
  plusCorr d beta (origin d) z ≤ plusCorrTailSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorr_le_tailSup beta n z hz

/--
[plusCorrTailSup_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorrTailSup_nonneg_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ plusCorrTailSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorrTailSup_nonneg beta n

/--
[plusCorrTailSup_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorrTailSup_le_one_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  plusCorrTailSup d beta n ≤ 1 := by
-- proof
  apply StatMech.Sharpness.plusCorrTailSup_le_one beta n

/--
[shifted_distance_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma shifted_distance_ge_eq
  {d : ℕ}
  {n R : ℕ}
  {y z : Site d}
-- given
  (hy : l1dist d (origin d) y < R)
  (hz : n + R ≤ l1dist d (origin d) z) :
-- imply
  n ≤ l1dist d (origin d) (z - y) := by
-- proof
  apply StatMech.Sharpness.shifted_distance_ge hy hz

/--
[plusCorrTailSup_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorrTailSup_step_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
  {n : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (ho : origin d ∈ T)
  (hn : 0 < n) :
-- imply
  plusCorrTailSup d beta (n + isingSimonRadius d T) ≤ phiIsing d beta T * plusCorrTailSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorrTailSup_step beta hbeta T ho n hn

/--
[plusCorrTailSup_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorrTailSup_geom_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (ho : origin d ∈ T) :
-- imply
  ∀ k : ℕ, plusCorrTailSup d beta (k * isingSimonRadius d T + 1) ≤ (phiIsing d beta T) ^ k := by
-- proof
  apply StatMech.Sharpness.plusCorrTailSup_geom beta hbeta T ho

/--
[plusCorr_exponential_of_phi_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorr_exponential_of_phi_lt_one_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (ho : origin d ∈ T)
  (hphi0 : 0 < phiIsing d beta T)
  (hphi1 : phiIsing d beta T < 1) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ z : Site d, plusCorr d beta (origin d) z ≤ C * Real.exp (-c * l1dist d (origin d) z) := by
-- proof
  apply StatMech.Sharpness.plusCorr_exponential_of_phi_lt_one beta hbeta T ho hphi0 hphi1

/--
[plusCorr_exponential_of_phi_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorr_exponential_of_phi_eq_zero_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (ho : origin d ∈ T)
  (hphi : phiIsing d beta T = 0) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ z : Site d, plusCorr d beta (origin d) z ≤ C * Real.exp (-c * l1dist d (origin d) z) := by
-- proof
  apply StatMech.Sharpness.plusCorr_exponential_of_phi_eq_zero beta hbeta T ho hphi

/--
[plusCorr_exponential_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorr_exponential_of_witness_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (ho : origin d ∈ T)
  (hphi : phiIsing d beta T < 1) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ z : Site d, plusCorr d beta (origin d) z ≤ C * Real.exp (-c * l1dist d (origin d) z) := by
-- proof
  apply StatMech.Sharpness.plusCorr_exponential_of_witness beta hbeta T ho hphi

/--
[plusCorr_absorb_exponential_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma plusCorr_absorb_exponential_prefactor_eq
  {d : ℕ}
  {beta : ℝ}
  {c₀ : ℝ}
  {C : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hsum : Summable (plusCorr d beta (origin d)))
  (hc₀ : 0 < c₀)
  (hC : 0 < C)
  (hdecay : ∀ z : Site d, plusCorr d beta (origin d) z ≤ C * Real.exp (-c₀ * l1dist d (origin d) z)) :
-- imply
  ∃ c > 0, ∀ z : Site d, plusCorr d beta (origin d) z ≤ Real.exp (-c * l1dist d (origin d) z) := by
-- proof
  apply StatMech.Sharpness.plusCorr_absorb_exponential_prefactor beta hbeta hsum c₀ hc₀ C hC hdecay

/--
[exponential_decay_with_prefactor_of_lt_tildeBetaCIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma exponential_decay_with_prefactor_of_lt_tildeBetaCIsing_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hlt : beta < tildeBetaCIsing d) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ z : Site d, plusCorr d beta (origin d) z ≤ C * Real.exp (-c * l1dist d (origin d) z) := by
-- proof
  apply StatMech.Sharpness.exponential_decay_with_prefactor_of_lt_tildeBetaCIsing hbeta hlt

/--
[exponential_decay_of_lt_tildeBetaCIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean)
-/
@[path]
private lemma exponential_decay_of_lt_tildeBetaCIsing_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hlt : beta < tildeBetaCIsing d) :
-- imply
  ∃ c > 0, ∀ z : Site d, plusCorr d beta (origin d) z ≤ Real.exp (-c * l1dist d (origin d) z) := by
-- proof
  apply StatMech.Sharpness.exponential_decay_of_lt_tildeBetaCIsing hbeta hlt


-- created on 2026-10-23
