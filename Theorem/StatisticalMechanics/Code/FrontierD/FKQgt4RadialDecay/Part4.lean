/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4Nonnegative_add_swap (x : Site 2) :
    fkQgt4NonnegativeSite x +
        (FK.rot_permBoxSym 2 (Equiv.swap (0 : Fin 2) 1)).τ
          (fkQgt4NonnegativeSite x) =
      fkQgt4ExactDiagonalSite (fkQgt4SiteRadius x) := by
  funext i
  fin_cases i <;>
    simp [fkQgt4NonnegativeSite_apply, fkQgt4SiteRadius,
      FK.rot_permBoxSym, FK.rot_permEquiv,
      fkQgt4ExactDiagonalSite] <;> omega


theorem fkQgt4CriticalFreeTwoPoint_sq_le_diagonal
    {q : Real} (hq : 4 < q) (x : Site 2) :
    fkQgt4CriticalFreeTwoPoint hq x ^ 2 <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq
        (fkQgt4SiteRadius x) := by
  let z := fkQgt4NonnegativeSite x
  let S := FK.rot_permBoxSym 2 (Equiv.swap (0 : Fin 2) 1)
  have hnorm : fkQgt4CriticalFreeTwoPoint hq z =
      fkQgt4CriticalFreeTwoPoint hq x := by
    dsimp [z]
    rw [← fkQgt4CoordinateSignBoxSym_normalizes x]
    exact fkQgt4CriticalFreeTwoPoint_boxSym hq _ x
  have hswap : fkQgt4CriticalFreeTwoPoint hq (S.τ z) =
      fkQgt4CriticalFreeTwoPoint hq z :=
    fkQgt4CriticalFreeTwoPoint_boxSym hq S z
  have hadd := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative
    hq z (S.τ z)
  rw [hswap, hnorm] at hadd
  rw [show z + S.τ z = fkQgt4ExactDiagonalSite
      (fkQgt4SiteRadius x) by
        simpa [z, S] using fkQgt4Nonnegative_add_swap x] at hadd
  simpa [pow_two, fkQgt4CriticalFreeTwoPoint,
    fkQgt4CriticalFreeExactDiagonalTwoPoint] using hadd


theorem fkQgt4CriticalFreeTwoPoint_eventually_exponential
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    exists N : Nat, forall x : Site 2, N <= fkQgt4SiteRadius x ->
      fkQgt4CriticalFreeTwoPoint hq x <=
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (fkQgt4SiteRadius x : Real)) := by
  let L := fkQgt4CriticalFreeExactDiagonalRateLimit hq
  have hhalf : L / 2 < L := by dsimp [L]; linarith
  have hevent : ∀ᶠ n : Nat in atTop,
      L / 2 <
        -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) /
          (n : Real) :=
    (fkQgt4CriticalFreeExactDiagonalRate_tendsto hq).eventually
      (Ioi_mem_nhds hhalf)
  rw [eventually_atTop] at hevent
  obtain ⟨N0, hN0⟩ := hevent
  refine ⟨max N0 1, ?_⟩
  intro x hx
  let n := fkQgt4SiteRadius x
  have hnN : N0 <= n := le_trans (Nat.le_max_left _ _) hx
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_one)
    (le_trans (Nat.le_max_right _ _) hx)
  have hrate := hN0 n hnN
  have hdiagpos := fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq n
  have hlog : Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) <
      -(L / 2) * (n : Real) := by
    have hnreal : (0 : Real) < n := by exact_mod_cast hnpos
    rw [lt_div_iff₀ hnreal] at hrate
    nlinarith
  have hdiag : fkQgt4CriticalFreeExactDiagonalTwoPoint hq n <=
      Real.exp (-(L / 2) * (n : Real)) := by
    exact (Real.log_lt_iff_lt_exp hdiagpos).mp hlog |>.le
  have hsq := fkQgt4CriticalFreeTwoPoint_sq_le_diagonal hq x
  have hpoint : 0 <= fkQgt4CriticalFreeTwoPoint hq x :=
    (fkQgt4CriticalFreeTwoPoint_pos hq x).le
  have hexp : 0 <= Real.exp (-(L / 4) * (n : Real)) :=
    (Real.exp_pos _).le
  have hexpSq :
      Real.exp (-(L / 4) * (n : Real)) ^ 2 =
        Real.exp (-(L / 2) * (n : Real)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquares : fkQgt4CriticalFreeTwoPoint hq x ^ 2 <=
      Real.exp (-(L / 4) * (n : Real)) ^ 2 := by
    rw [hexpSq]
    exact hsq.trans hdiag
  have := (sq_le_sq₀ hpoint hexp).mp hsquares
  simpa [L, n] using this


theorem fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    exists N : Nat, forall n : Nat, N <= n ->
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (fkQgt4CriticalFreeSphereConnectionEvent n) <=
        ((2 * n + 1 : Nat) : Real) ^ 2 *
          Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
            (n : Real)) := by
  obtain ⟨N, hN⟩ :=
    fkQgt4CriticalFreeTwoPoint_eventually_exponential hq hpos
  refine ⟨N, ?_⟩
  intro n hn
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  calc
    mu.real (fkQgt4CriticalFreeSphereConnectionEvent n) <=
        ∑ x ∈ fkQgt4SiteSphere n,
          mu.real {omega | Connected 2 omega (origin 2) x} := by
      exact measureReal_biUnion_finset_le _ _
    _ <= ∑ _x ∈ fkQgt4SiteSphere n,
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (n : Real)) := by
      apply Finset.sum_le_sum
      intro x hx
      have hradius : fkQgt4SiteRadius x = n :=
        (Finset.mem_filter.mp hx).2
      change fkQgt4CriticalFreeTwoPoint hq x <= _
      simpa [hradius] using hN x (hradius.symm ▸ hn)
    _ = ((fkQgt4SiteSphere n).card : Real) *
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (n : Real)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ((2 * n + 1 : Nat) : Real) ^ 2 *
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (n : Real)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast fkQgt4SiteSphere_card_le n

end
end StatMech.FrontierD
