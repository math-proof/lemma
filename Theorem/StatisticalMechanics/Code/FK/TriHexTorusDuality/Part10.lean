/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part9
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorus_sectorSum_duality (L : ℕ) [Fact (2 < L)]
    (r : ℤ) (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexTorusPrimalSectorSum L r p q F *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F * q ^ r := by
  classical
  unfold triHexTorusPrimalSectorSum triHexTorusDualSectorSum
  rw [Finset.sum_mul]
  calc
    ∑ omega, (if triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) = r then
        F (triHexTorusDualConfig L omega) *
          FK.fkWeight (triangularTorusGraph L) p q omega
      else 0) * q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
        ∑ omega,
          (p / (1 - BeffaraDC.dualParam p q)) ^
              (triangularTorusGraph L).edgeFinset.card *
            q ^ Nat.card (TorusSite L) *
            (if triHexTorusDefect L
                (FK.openSub (triangularTorusGraph L) omega) = r then
              F (triHexTorusDualConfig L omega) *
                FK.fkWeight (hexagonalTorusGraph L)
                  (BeffaraDC.dualParam p q) q
                  (triHexTorusDualConfig L omega)
            else 0) * q ^ r := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases hsector : triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) = r
      · simp only [hsector, if_true]
        have hweight := triHexTorus_fkWeight_duality_signed L omega hp hp1 hq
        rw [hsector] at hweight
        calc
          (F (triHexTorusDualConfig L omega) *
              FK.fkWeight (triangularTorusGraph L) p q omega) *
              q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
              F (triHexTorusDualConfig L omega) *
                (FK.fkWeight (triangularTorusGraph L) p q omega *
                  q ^ ((triangularTorusGraph L).edgeFinset.card + 1)) := by ring
          _ = F (triHexTorusDualConfig L omega) *
              ((p / (1 - BeffaraDC.dualParam p q)) ^
                  (triangularTorusGraph L).edgeFinset.card *
                q ^ Nat.card (TorusSite L) *
                FK.fkWeight (hexagonalTorusGraph L)
                  (BeffaraDC.dualParam p q) q
                  (triHexTorusDualConfig L omega) * q ^ r) := by rw [hweight]
          _ = (p / (1 - BeffaraDC.dualParam p q)) ^
                  (triangularTorusGraph L).edgeFinset.card *
                q ^ Nat.card (TorusSite L) *
                (F (triHexTorusDualConfig L omega) *
                  FK.fkWeight (hexagonalTorusGraph L)
                    (BeffaraDC.dualParam p q) q
                    (triHexTorusDualConfig L omega)) * q ^ r := by ring
      · simp [hsector]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        (∑ omega, if triHexTorusDefect L
              (FK.openSub (triangularTorusGraph L) omega) = r then
            F (triHexTorusDualConfig L omega) *
              FK.fkWeight (hexagonalTorusGraph L)
                (BeffaraDC.dualParam p q) q
                (triHexTorusDualConfig L omega)
          else 0) * q ^ r := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]


theorem triHexTorus_sectorPartition_duality (L : ℕ) [Fact (2 < L)]
    (r : ℤ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexTorusPrimalSectorSum L r p q (fun _ => 1) *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1) * q ^ r :=
  triHexTorus_sectorSum_duality L r (fun _ => 1) hp hp1 hq


theorem triHexTorus_sectorNormalized_duality (L : ℕ) [Fact (2 < L)]
    (r : ℤ) (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hprimal : triHexTorusPrimalSectorSum L r p q (fun _ => 1) ≠ 0)
    (hdual : triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
      (fun _ => 1) ≠ 0) :
    triHexTorusPrimalSectorSum L r p q F /
        triHexTorusPrimalSectorSum L r p q (fun _ => 1) =
      triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F /
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1) := by
  let A := q ^ ((triangularTorusGraph L).edgeFinset.card + 1)
  let B := (p / (1 - BeffaraDC.dualParam p q)) ^
      (triangularTorusGraph L).edgeFinset.card *
    q ^ Nat.card (TorusSite L) * q ^ r
  have hA : A ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt hq)
  have hnum := triHexTorus_sectorSum_duality L r F hp hp1 hq
  have hpart := triHexTorus_sectorPartition_duality L r hp hp1 hq
  have hnum' : triHexTorusPrimalSectorSum L r p q F * A =
      B * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F := by
    dsimp only [A, B]
    linarith
  have hpart' : triHexTorusPrimalSectorSum L r p q (fun _ => 1) * A =
      B * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
        (fun _ => 1) := by
    dsimp only [A, B]
    linarith
  apply (div_eq_div_iff hprimal hdual).2
  apply mul_right_cancel₀ hA
  calc
    (triHexTorusPrimalSectorSum L r p q F *
          triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
            (fun _ => 1)) * A =
        (triHexTorusPrimalSectorSum L r p q F * A) *
          triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
            (fun _ => 1) := by ring
    _ = (B * triHexTorusDualSectorSum L r
          (BeffaraDC.dualParam p q) q F) *
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1) := by rw [hnum']
    _ = triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F *
        (B * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1)) := by ring
    _ = triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F *
        (triHexTorusPrimalSectorSum L r p q (fun _ => 1) * A) := by
      rw [hpart']
    _ = (triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F *
          triHexTorusPrimalSectorSum L r p q (fun _ => 1)) * A := by
      ring

end PeriodicPlanar
end FK
end StatMech
