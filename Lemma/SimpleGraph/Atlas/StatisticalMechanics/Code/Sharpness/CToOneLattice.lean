import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
open Filter Topology StatMech StatMech.Sharpness


/--
[sctBoxInclusionEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctBoxInclusionEquiv_adj_eq
  {d : ℕ}
  {n m : ℕ}
  {a b : sctBox d n}
-- given
  (hnm : n ≤ m) :
-- imply
  (sctBoxGraph d n).Adj a b ↔ ((sctBoxGraph d m).comap (Subtype.val : {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)).Adj (sctBoxInclusionEquiv d hnm a) (sctBoxInclusionEquiv d hnm b) := by
-- proof
  apply StatMech.Sharpness.sctBoxInclusionEquiv_adj d hnm a b

/--
[sctTranslatedInDoubleEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctTranslatedInDoubleEquiv_adj_eq
  {d n : ℕ}
  {y : sctBox d n}
-- given
  (a b : {z : Site d // z ∈ sctTranslatedBox d n y.1}) :
-- imply
  (sctTranslatedBoxGraph d n y.1).Adj a b ↔ ((sctBoxGraph d (2 * n)).comap (Subtype.val : {z : sctBox d (2 * n) // sctTranslatedInDouble d n y z} → sctBox d (2 * n))).Adj (sctTranslatedInDoubleEquiv d n y a) (sctTranslatedInDoubleEquiv d n y b) := by
-- proof
  apply StatMech.Sharpness.sctTranslatedInDoubleEquiv_adj d n y a b

/--
[sctTranslateEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctTranslateEquiv_adj_eq
  {d n : ℕ}
  {y : Site d}
  {a b : sctBox d n} :
-- imply
  (sctBoxGraph d n).Adj a b ↔ (sctTranslatedBoxGraph d n y).Adj (sctTranslateEquiv d n y a) (sctTranslateEquiv d n y b) := by
-- proof
  apply StatMech.Sharpness.sctTranslateEquiv_adj d n y a b

/--
[sctBoxSites_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctBoxSites_nonempty_eq
  {d n : ℕ} :
-- imply
  (sctBoxSites d n).Nonempty := by
-- proof
  apply StatMech.Sharpness.sctBoxSites_nonempty d n

/--
[sctBoxMag_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctBoxMag_origin_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ) :
-- imply
  sctBoxMag d β h n (sctBoxOrigin d n) = sctOriginMag d β h n := by
-- proof
  apply StatMech.Sharpness.sctBoxMag_origin d β h n

/--
[sctBoxMag_eq_translated_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctBoxMag_eq_translated_origin_eq
  {d : ℕ}
  {n : ℕ}
  {x : sctBox d n}
-- given
  (β h : ℝ) :
-- imply
  sctBoxMag d β h n x = isingExpectation (sctTranslatedBoxGraph d n x.1) β h (fun s => spin s (sctTranslateEquiv d n x.1 x)) := by
-- proof
  apply StatMech.Sharpness.sctBoxMag_eq_translated_origin d β h n x

/--
[sctTranslateEquiv_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctTranslateEquiv_self_eq
  {d : ℕ}
  {n : ℕ}
  {x : sctBox d n} :
-- imply
  (sctTranslateEquiv d n x.1 x).1 = (fun _ => 0 : Site d) := by
-- proof
  apply StatMech.Sharpness.sctTranslateEquiv_self d n x

/--
[sctBoxMag_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctBoxMag_pos_eq
  {d : ℕ}
  {n : ℕ}
  {x : sctBox d n}
-- given
  (β h : ℝ)
  (hβ : 0 < β)
  (hh : 0 < h) :
-- imply
  0 < sctBoxMag d β h n x := by
-- proof
  apply StatMech.Sharpness.sctBoxMag_pos d β h hβ hh n x

/--
[sctOriginMag_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctOriginMag_pos_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 < β)
  (hh : 0 < h) :
-- imply
  0 < sctOriginMag d β h n := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_pos d β h hβ hh n

/--
[sctOriginMag_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctOriginMag_le_one_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ) :
-- imply
  sctOriginMag d β h n ≤ 1 := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_le_one d β h n

/--
[sctOriginMag_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctOriginMag_monotone_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  Monotone (sctOriginMag d β h) := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_monotone d β h hβ hh

/--
[sctBoxMag_le_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctBoxMag_le_double_eq
  {d : ℕ}
  {n : ℕ}
  {x : sctBox d n}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  sctBoxMag d β h n x ≤ sctOriginMag d β h (2 * n) := by
-- proof
  apply StatMech.Sharpness.sctBoxMag_le_double d β h hβ hh n x

/--
[sctLatticeC_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctLatticeC_le_one_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 < β)
  (hh : 0 < h) :
-- imply
  sctLatticeC d β h n ≤ 1 := by
-- proof
  apply StatMech.Sharpness.sctLatticeC_le_one d β h hβ hh n

/--
[sctLatticeC_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean)
-/
@[path]
private lemma sctLatticeC_tendsto_one_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 < β)
  (hh : 0 < h) :
-- imply
  Tendsto (sctLatticeC d β h) atTop (𝓝 1) := by
-- proof
  apply StatMech.Sharpness.sctLatticeC_tendsto_one d β h hβ hh


-- created on 2026-10-23
