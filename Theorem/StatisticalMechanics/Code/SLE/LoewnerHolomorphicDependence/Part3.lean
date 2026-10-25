/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part15
import Mathlib.Analysis.Complex.Conformal
import Def.StatisticalMechanics.Code.SLE.LoewnerHolomorphicDependence.Part2
open Complex Set Metric Filter Topology
open scoped Interval


namespace StatMech.SLE

noncomputable section

theorem hasLoewnerLocalInitialVariationalFormula
    {W : Real -> Real} (hW : Continuous W) :
    HasLoewnerLocalInitialVariationalFormula W := by
  intro s u z hu hz hshort
  exact loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen
    (hW.comp (continuous_const.add continuous_id)) hu hz hshort


theorem exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    exists c : Complex, c ≠ 0 /\
      HasDerivAt (loewnerMaximalMaps W t) c z := by
  let delta : Real := (loewnerMaximalMaps W t z).im
  have hdelta : 0 < delta :=
    mem_upperHalfPlane.mp (loewnerMaximalMaps_mem_upperHalfPlane hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / delta ^ 2)
  have hquot : 0 <= 16 * t / delta ^ 2 := by positivity
  have hn0 : 0 < (n : Real) := hquot.trans_lt hn
  let u : Real := t / (n : Real)
  have hu : 0 <= u := by dsimp [u]; positivity
  have hnu : (n : Real) * u = t := by
    dsimp [u]
    field_simp
  have hushort : u < delta ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : Real) * delta ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hdelta)).mp hn
    nlinarith
  have htime (k : Nat) (hk : k <= n) :
      0 <= (k : Real) * u ∧ (k : Real) * u <= t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg k) hu, ?_⟩
    rw [<- hnu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hu
  have hsurvives (k : Nat) (hk : k <= n) :
      z ∈ loewnerUnswallowedDomain W ((k : Real) * u) :=
    loewnerUnswallowedDomain_antitoneOn W (htime k hk).1 ht
      (htime k hk).2 hz
  have hind : forall k : Nat, k <= n ->
      exists c : Complex, c ≠ 0 /\
        HasDerivAt (loewnerMaximalMaps W ((k : Real) * u)) c z := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨1, one_ne_zero, ?_⟩
        simpa using loewnerMaximalMaps_hasDerivAt_initial_zero hW hz.1
    | succ k ih =>
        intro hkn
        have hk : k <= n := (Nat.le_succ k).trans hkn
        obtain ⟨c, hc, hderiv⟩ := ih hk
        let s : Real := (k : Real) * u
        let y : Complex := loewnerMaximalMaps W s z
        have hs : 0 <= s := (htime k hk).1
        have hstepTime : ((k + 1 : Nat) : Real) * u = s + u := by
          dsimp [s]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hznext : z ∈ loewnerUnswallowedDomain W (s + u) := by
          rw [<- hstepTime]
          exact hsurvives (k + 1) hkn
        have hysurvives : y ∈
            loewnerUnswallowedDomain (fun r => W (s + r)) u :=
          loewnerMaximalMaps_mem_shiftedUnswallowedDomain hs hu hznext
        have hy : y ∈ upperHalfPlane := hysurvives.1
        have him : delta <= y.im := by
          exact loewnerMaximalCurve_im_antitoneOn
            (hsurvives k hk).2 hz.2 (htime k hk).2
        have hshort : u < y.im ^ 2 / 16 := by
          calc
            u < delta ^ 2 / 16 := hushort
            _ <= y.im ^ 2 / 16 := by gcongr
        have hlocalDeriv := hlocal s u y hu hy hshort
        have hderivS : HasDerivAt (loewnerMaximalMaps W s) c z := by
          simpa [s] using hderiv
        have hcomp : HasDerivAt
            (fun w => loewnerMaximalMaps (fun r => W (s + r)) u
              (loewnerMaximalMaps W s w))
            (loewnerInitialJacobian (fun r => W (s + r)) u y * c) z :=
          by simpa [Function.comp_def] using hlocalDeriv.comp z hderivS
        have heq : loewnerMaximalMaps W (s + u) =ᶠ[nhds z]
            (fun w => loewnerMaximalMaps (fun r => W (s + r)) u
              (loewnerMaximalMaps W s w)) := by
          filter_upwards [
            (isOpen_loewnerUnswallowedDomain hW (add_nonneg hs hu)).mem_nhds
              hznext] with w hw
          exact loewnerMaximalMaps_flow hs hu hw
        refine ⟨loewnerInitialJacobian (fun r => W (s + r)) u y * c,
          mul_ne_zero (loewnerInitialJacobian_ne_zero _ _ _) hc, ?_⟩
        rw [hstepTime]
        exact hcomp.congr_of_eventuallyEq heq
  obtain ⟨c, hc, hderiv⟩ := hind n le_rfl
  rw [hnu] at hderiv
  exact ⟨c, hc, hderiv⟩


theorem loewnerMaximalMaps_differentiableOn_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) :
    DifferentiableOn Complex (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) := by
  intro z hz
  obtain ⟨c, _hc, hderiv⟩ :=
    exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
      hW hlocal ht hz
  exact hderiv.differentiableAt.differentiableWithinAt


theorem loewnerMaximalMaps_conformalAt_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ConformalAt (loewnerMaximalMaps W t) z := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
      hW hlocal ht hz
  apply hderiv.differentiableAt.conformalAt
  rw [hderiv.deriv]
  exact hc


theorem loewnerMaximalMaps_conformalOn_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) :
    forall z, z ∈ loewnerUnswallowedDomain W t ->
      ConformalAt (loewnerMaximalMaps W t) z := by
  intro z hz
  exact loewnerMaximalMaps_conformalAt_of_localVariational
    hW hlocal ht hz


theorem exists_loewnerMaximalMaps_hasDerivAt_ne_zero
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    exists c : Complex, c ≠ 0 /\
      HasDerivAt (loewnerMaximalMaps W t) c z :=
  exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht hz


theorem loewnerMaximalMaps_differentiableOn
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) :
    DifferentiableOn Complex (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) :=
  loewnerMaximalMaps_differentiableOn_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht


theorem loewnerMaximalMaps_conformalAt
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ConformalAt (loewnerMaximalMaps W t) z :=
  loewnerMaximalMaps_conformalAt_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht hz


theorem loewnerMaximalMaps_conformalOn
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) :
    forall z, z ∈ loewnerUnswallowedDomain W t ->
      ConformalAt (loewnerMaximalMaps W t) z := by
  intro z hz
  exact loewnerMaximalMaps_conformalAt hW ht hz

end
end StatMech.SLE
