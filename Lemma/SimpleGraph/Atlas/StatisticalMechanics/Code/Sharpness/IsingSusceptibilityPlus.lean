import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSusceptibilityPlus.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech StatMech.Sharpness


/--
[plusCorr_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorr_shift_eq
  {d : ℕ}
  {beta : ℝ}
  {g : Multiplicative (Site d)}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  plusCorr d beta (g • x) (g • y) = plusCorr d beta x y := by
-- proof
  apply StatMech.Sharpness.plusCorr_shift beta hbeta g x y

/--
[gvPlus_pair_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma gvPlus_pair_nonneg_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (a b : {v // v ∈ Lambda}) :
-- imply
  0 ≤ ∫ omega, spin omega a.1 * spin omega b.1 ∂(gvPlusMeasure Lambda beta 0) := by
-- proof
  apply StatMech.Sharpness.gvPlus_pair_nonneg Lambda beta hbeta a b

/--
[plusCorr_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorr_nonneg_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  0 ≤ plusCorr d beta x y := by
-- proof
  apply StatMech.Sharpness.plusCorr_nonneg beta hbeta x y

/--
[plusCorr_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorr_le_one_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d} :
-- imply
  plusCorr d beta x y ≤ 1 := by
-- proof
  apply StatMech.Sharpness.plusCorr_le_one beta x y

/--
[plusCorr_eq_origin_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorr_eq_origin_translate_eq
  {d : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  plusCorr d beta x y = plusCorr d beta (Percolation.origin d) (y - x) := by
-- proof
  apply StatMech.Sharpness.plusCorr_eq_origin_translate beta hbeta x y

/--
[plusCorrWindowSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorrWindowSet_nonempty_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  ({r : ℝ | ∃ L : Finset (Site d), L.card ≤ n ∧ r = plusCorrWindowSum d beta L} : Set ℝ).Nonempty := by
-- proof
  apply StatMech.Sharpness.plusCorrWindowSet_nonempty beta n

/--
[plusCorrWindowSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorrWindowSet_bddAbove_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  BddAbove {r : ℝ | ∃ L : Finset (Site d), L.card ≤ n ∧ r = plusCorrWindowSum d beta L} := by
-- proof
  apply StatMech.Sharpness.plusCorrWindowSet_bddAbove beta n

/--
[plusCorrWindowSum_le_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorrWindowSum_le_sup_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ}
  {L : Finset (Site d)}
-- given
  (hcard : L.card ≤ n) :
-- imply
  plusCorrWindowSum d beta L ≤ plusCorrWindowSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorrWindowSum_le_sup beta n L hcard

/--
[plusCorrWindowSup_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorrWindowSup_nonneg_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ plusCorrWindowSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorrWindowSup_nonneg beta n

/--
[plusCorr_translatedWindow_le_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorr_translatedWindow_le_sup_eq
  {d : ℕ}
  {beta : ℝ}
  {n : ℕ}
  {L : Finset (Site d)}
  {y : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hcard : L.card ≤ n) :
-- imply
  (∑ z ∈ L, plusCorr d beta y z) ≤ plusCorrWindowSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorr_translatedWindow_le_sup beta hbeta n L hcard y

/--
[plusCorrWindowSum_self_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorrWindowSum_self_bound_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
  {L : Finset (Site d)}
  {n : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (ho : Percolation.origin d ∈ T)
  (hcard : L.card ≤ n) :
-- imply
  plusCorrWindowSum d beta L ≤ (T.card : ℝ) + phiIsing d beta T * plusCorrWindowSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorrWindowSum_self_bound beta hbeta T ho L n hcard

/--
[plusCorrWindowSup_self_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorrWindowSup_self_bound_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
  {n : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (ho : Percolation.origin d ∈ T) :
-- imply
  plusCorrWindowSup d beta n ≤ (T.card : ℝ) + phiIsing d beta T * plusCorrWindowSup d beta n := by
-- proof
  apply StatMech.Sharpness.plusCorrWindowSup_self_bound beta hbeta T ho n

/--
[plusCorr_summable_of_phi_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma plusCorr_summable_of_phi_lt_one_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (ho : Percolation.origin d ∈ T)
  (hphi : phiIsing d beta T < 1) :
-- imply
  Summable (plusCorr d beta (Percolation.origin d)) := by
-- proof
  apply StatMech.Sharpness.plusCorr_summable_of_phi_lt_one beta hbeta T ho hphi

/--
[freeCorr_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma freeCorr_mono_beta_eq
  {d : ℕ}
  {beta gamma : ℝ}
  {S : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (hbg : beta ≤ gamma)
  (a b : {v // v ∈ S}) :
-- imply
  freeCorr d beta S a b ≤ freeCorr d gamma S a b := by
-- proof
  apply StatMech.Sharpness.freeCorr_mono_beta hbeta hbg S a b

/--
[corrOriginInner_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma corrOriginInner_mono_beta_eq
  {d : ℕ}
  {beta gamma : ℝ}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hbg : beta ≤ gamma) :
-- imply
  corrOriginInner d beta S x ≤ corrOriginInner d gamma S x := by
-- proof
  apply StatMech.Sharpness.corrOriginInner_mono_beta hbeta hbg S x

/--
[phiIsing_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma phiIsing_mono_eq
  {d : ℕ}
  {beta gamma : ℝ}
  {S : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (hbg : beta ≤ gamma) :
-- imply
  phiIsing d beta S ≤ phiIsing d gamma S := by
-- proof
  apply StatMech.Sharpness.phiIsing_mono hbeta hbg S

/--
[exists_phiIsing_witness_of_lt_tildeBetaCIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma exists_phiIsing_witness_of_lt_tildeBetaCIsing_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hlt : beta < tildeBetaCIsing d) :
-- imply
  ∃ S : Finset (Site d), Percolation.origin d ∈ S ∧ phiIsing d beta S < 1 := by
-- proof
  apply StatMech.Sharpness.exists_phiIsing_witness_of_lt_tildeBetaCIsing hbeta hlt

/--
[finite_susceptibility_of_lt_tildeBetaCIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean)
-/
@[path]
private lemma finite_susceptibility_of_lt_tildeBetaCIsing_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hlt : beta < tildeBetaCIsing d) :
-- imply
  ∃ S : Finset (Site d), Percolation.origin d ∈ S ∧ phiIsing d beta S < 1 ∧ Summable (plusCorr d beta (Percolation.origin d)) := by
-- proof
  apply StatMech.Sharpness.finite_susceptibility_of_lt_tildeBetaCIsing hbeta hlt


-- created on 2026-10-23
