import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part3
open StatMech StatMech.Universality StatMech.Universality.HexEndpointSideFibers


/--
[hecd_columnSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean)
-/
@[path]
private lemma hecd_columnSum_nonneg_eq
  {a : ℂ}
  {scale : {ts : List ℤ // P ts} → ℕ}
  {v : ℕ}
-- given
  (h0 : ℤ)
  (P : List ℤ → Prop) :
-- imply
  0 ≤ hecd_columnSum a h0 P scale v := by
-- proof
  apply StatMech.Universality.hecd_columnSum_nonneg a h0 P scale v

/--
[hecd_columnSum_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean)
-/
@[path]
private lemma hecd_columnSum_summable_eq
  {a : ℂ}
  {scale : {ts : List ℤ // P ts} → ℕ}
-- given
  (h0 : ℤ)
  (P : List ℤ → Prop)
  (hwalk : Summable (hexEndpointSAWwt a h0 hexChiE)) :
-- imply
  Summable (hecd_columnSum a h0 P scale) := by
-- proof
  apply StatMech.Universality.hecd_columnSum_summable a h0 P scale hwalk

/--
[sidePred_height_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean)
-/
@[path]
private lemma sidePred_height_unique_eq
  {a : ℂ}
  {h0 : ℤ}
  {S : HexEndpointSideFibers a h0}
  {T L L' : ℕ}
  {ts : List ℤ}
-- given
  (hL : S.sidePred T L ts)
  (hL' : S.sidePred T L' ts) :
-- imply
  L = L' := by
-- proof
  apply StatMech.Universality.HexEndpointSideFibers.sidePred_height_unique S T L L' ts hL hL'

/--
[hecd_side_limit_forces_walk_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean)
-/
@[path]
private lemma hecd_side_limit_forces_walk_divergence_eq
  {a : ℂ}
  {h0 : ℤ}
  {tau : ℕ → ℝ}
  {S : HexEndpointSideLimits a h0 tau}
-- given
  (hpos : ∃ T, 1 ≤ T ∧ 0 < tau T) :
-- imply
  ¬ Summable (hexEndpointSAWwt a h0 hexChiE) := by
-- proof
  apply StatMech.Universality.hecd_side_limit_forces_walk_divergence S hpos

/--
[hecd_critical_divergence_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean)
-/
@[path]
private lemma hecd_critical_divergence_of_recurrence_eq
  {a : ℂ}
  {lam tau : ℕ → ℝ}
  {scale : {ts : List ℤ // Pcol ts} → ℕ}
  {S : HexEndpointSideLimits a h0 tau}
-- given
  (h0 : ℤ)
  (Pcol : List ℤ → Prop)
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + hecd_columnSum a h0 Pcol scale v = 1)
  (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE⁻¹ * (hecd_columnSum a h0 Pcol scale (v + 1)) ^ 2)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hcolPos : ∀ v, 1 ≤ v → 0 < hecd_columnSum a h0 Pcol scale v)
  (hτnn : ∀ v, 0 ≤ tau v) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hecd_critical_divergence_of_recurrence a h0 lam tau Pcol scale S hbdry hrec hlamMono hcolPos hτnn


-- created on 2026-10-23
