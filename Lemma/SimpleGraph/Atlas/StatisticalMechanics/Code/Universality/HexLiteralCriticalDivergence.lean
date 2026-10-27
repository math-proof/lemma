import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence.Part5
open StatMech StatMech.Universality StatMech.Universality.HexLiteralSideFibers


/--
[hlcd_not_summable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_not_summable_iff_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  (¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n)) ↔ ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) := by
-- proof
  apply StatMech.Universality.hlcd_not_summable_iff a h0 hx

/--
[hlcd_not_summable_of_literal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_not_summable_of_literal_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hdiv : ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 x ts)) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlcd_not_summable_of_literal a h0 hx hdiv

/--
[hlcd_columnSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_columnSum_nonneg_eq
  {a : ℂ}
  {scale : {ts : List ℤ // P ts} → ℕ}
  {v : ℕ}
-- given
  (h0 : ℤ)
  (P : List ℤ → Prop) :
-- imply
  0 ≤ hlcd_columnSum a h0 P scale v := by
-- proof
  apply StatMech.Universality.hlcd_columnSum_nonneg a h0 P scale v

/--
[hlcd_columnSum_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_columnSum_summable_eq
  {a : ℂ}
  {scale : {ts : List ℤ // P ts} → ℕ}
-- given
  (h0 : ℤ)
  (P : List ℤ → Prop)
  (hwalk : Summable (fun ts : List ℤ => hexSAWwt a h0 hexChiE ts)) :
-- imply
  Summable (hlcd_columnSum a h0 P scale) := by
-- proof
  apply StatMech.Universality.hlcd_columnSum_summable a h0 P scale hwalk

/--
[sidePred_height_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma sidePred_height_unique_eq
  {a : ℂ}
  {h0 : ℤ}
  {S : HexLiteralSideFibers a h0}
  {T L L' : ℕ}
  {ts : List ℤ}
-- given
  (hL : S.sidePred T L ts)
  (hL' : S.sidePred T L' ts) :
-- imply
  L = L' := by
-- proof
  apply StatMech.Universality.HexLiteralSideFibers.sidePred_height_unique S T L L' ts hL hL'

/--
[hlcd_side_limit_forces_literal_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_side_limit_forces_literal_divergence_eq
  {a : ℂ}
  {h0 : ℤ}
  {tau : ℕ → ℝ}
  {S : HexLiteralSideLimits a h0 tau}
-- given
  (hpos : ∃ T, 1 ≤ T ∧ 0 < tau T) :
-- imply
  ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 hexChiE ts) := by
-- proof
  apply StatMech.Universality.hlcd_side_limit_forces_literal_divergence S hpos

/--
[hlcd_ups_atScale_eq_columnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_ups_atScale_eq_columnSum_eq
  {a : ℂ}
  {scale : {ts : List ℤ // P ts} → ℕ}
  {v : ℕ}
-- given
  (h0 : ℤ)
  (P : List ℤ → Prop) :
-- imply
  hpb_upsS a h0 hexChiE (hlcd_atScale P scale v) = hlcd_columnSum a h0 P scale v := by
-- proof
  apply StatMech.Universality.hlcd_ups_atScale_eq_columnSum a h0 P scale v

/--
[hlcd_boundary_of_reflected_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_boundary_of_reflected_pairing_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {A : S.DCSAngles}
  {lam tau ups : ℝ}
-- given
  (S : HexFiniteStripReflectedPairing (ι := I) C)
  (hlam : lam = HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData (A.toClassification S))
  (htau : tau = HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData (A.toClassification S))
  (hups : ups = HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData (A.toClassification S)) :
-- imply
  hexCl * lam + hexCt * tau + ups = 1 := by
-- proof
  apply StatMech.Universality.hlcd_boundary_of_reflected_pairing S A lam tau ups hlam htau hups

/--
[hlcd_boundary_of_mirror_orbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_boundary_of_mirror_orbits_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {A : S.DCSClassification}
  {lam tau ups : ℝ}
-- given
  (S : HexFiniteStripMirrorOrbitData (I := I) (K := K) C)
  (hlam : lam = S.dcsLam A)
  (htau : tau = S.dcsTau A)
  (hups : ups = S.dcsUps A) :
-- imply
  hexCl * lam + hexCt * tau + ups = 1 := by
-- proof
  apply StatMech.Universality.hlcd_boundary_of_mirror_orbits S A lam tau ups hlam htau hups

/--
[hlcd_critical_divergence_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_critical_divergence_of_recurrence_eq
  {a : ℂ}
  {lam tau : ℕ → ℝ}
  {scale : {ts : List ℤ // Pcol ts} → ℕ}
  {S : HexLiteralSideLimits a h0 tau}
-- given
  (h0 : ℤ)
  (Pcol : List ℤ → Prop)
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + hlcd_columnSum a h0 Pcol scale v = 1)
  (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE⁻¹ * (hlcd_columnSum a h0 Pcol scale (v + 1)) ^ 2)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
  (hτnn : ∀ v, 0 ≤ tau v) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hlcd_critical_divergence_of_recurrence a h0 lam tau Pcol scale S hbdry hrec hlamMono hcolPos hτnn

/--
[hlcd_critical_divergence_of_cuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_critical_divergence_of_cuts_eq
  {a : ℂ}
  {lam tau : ℕ → ℝ}
  {scale : {ts : List ℤ // Pcol ts} → ℕ}
  {S : HexLiteralSideLimits a h0 tau}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
-- given
  (h0 : ℤ)
  (Pcol : List ℤ → Prop)
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + hlcd_columnSum a h0 Pcol scale v = 1)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
  (hτnn : ∀ v, 0 ≤ tau v)
  (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
  (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hlcd_columnSum a h0 Pcol scale (v + 1)) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hlcd_critical_divergence_of_cuts a h0 lam tau Pcol scale S hbdry hlamMono hcolPos hτnn Cut hCutD hCutB

/--
[hlcd_critical_divergence_of_half_classes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_critical_divergence_of_half_classes_eq
  {a : ℂ}
  {scale : {ts : List ℤ // Pcol ts} → ℕ}
  {tau : ℕ → ℝ}
  {S : HexLiteralSideLimits a h0 tau}
-- given
  (h0 : ℤ)
  (memA : ℕ → List ℤ → Prop)
  (Pcol : List ℤ → Prop)
  (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
  (HC : ∀ v, HexHalfClass a h0 hexChiE (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (hlcd_atScale Pcol scale (v + 1)))
  (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : ∀ v, Summable (fun b : {ts // hlcd_atScale Pcol scale (v + 1) ts} => hexSAWwt a h0 hexChiE b.1))
  (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a h0 hexChiE n.1))
  (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a h0 hexChiE (memA v) + hexCt * tau v + hlcd_columnSum a h0 Pcol scale v = 1)
  (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a h0 hexChiE (memA v) ≤ hpb_lamS a h0 hexChiE (memA (v + 1)))
  (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
  (hτnn : ∀ v, 0 ≤ tau v) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hlcd_critical_divergence_of_half_classes a h0 memA Pcol scale tau S hsub HC hDsum hBsum hAsum hbdry hlamMono hcolPos hτnn

/--
[hlcd_critical_divergence_of_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean)
-/
@[path]
private lemma hlcd_critical_divergence_of_halves_eq
  {a : ℂ}
  {scale : {ts : List ℤ // Pcol ts} → ℕ}
  {tau : ℕ → ℝ}
  {S : HexLiteralSideLimits a h0 tau}
-- given
  (h0 : ℤ)
  (memA : ℕ → List ℤ → Prop)
  (Pcol : List ℤ → Prop)
  (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
  (HIC : ∀ v, HexHalvesInColumn h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (hlcd_atScale Pcol scale (v + 1)))
  (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : ∀ v, Summable (fun b : {ts // hlcd_atScale Pcol scale (v + 1) ts} => hexSAWwt a h0 hexChiE b.1))
  (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a h0 hexChiE n.1))
  (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a h0 hexChiE (memA v) + hexCt * tau v + hlcd_columnSum a h0 Pcol scale v = 1)
  (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a h0 hexChiE (memA v) ≤ hpb_lamS a h0 hexChiE (memA (v + 1)))
  (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
  (hτnn : ∀ v, 0 ≤ tau v) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hlcd_critical_divergence_of_halves a h0 memA Pcol scale tau S hsub HIC hDsum hBsum hAsum hbdry hlamMono hcolPos hτnn


-- created on 2026-10-23
