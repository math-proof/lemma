/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterGhostLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzFourPoint
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness StatMech.FrontierA

open StatMech.Sharpness.FieldGhostDict

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem lpGhost_ursell4_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (i j k l : V) :
    grahamUrsell4 (withGhost G).edgeFinset (lpGhostCoupling J hf)
        (some i) (some j) (some k) (some l) =
      lpFieldUrsell4 G J hf i j k l := by
  unfold grahamUrsell4 lpFieldUrsell4
  rw [lpGhost_fourPoint_eq,
    lpGhost_twoPoint_eq, lpGhost_twoPoint_eq, lpGhost_twoPoint_eq,
    lpGhost_twoPoint_eq, lpGhost_twoPoint_eq, lpGhost_twoPoint_eq]

theorem lpGhostCoupling_nonneg
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x) :
    forall e, 0 <= lpGhostCoupling J hf e := by
  intro e
  induction e with
  | h a b =>
      rcases a with _ | x <;> rcases b with _ | y <;>
        simp [lpGhostCoupling, hJ, hhf]


theorem lpField_lebowitz_four_point_le_leading
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x)
    (i j k l : V)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    lpFieldUrsell4 G J hf i j k l <=
      -2 *
        (expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
          expJ G.edgeFinset J hf (fun s => spin s j * spin s l) *
          expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) := by
  have hlead := lebowitz_four_point_le_leading (withGhost G)
    (lpGhostCoupling J hf) (lpGhostCoupling_nonneg J hf hJ hhf)
    (some i) (some j) (some k) (some l)
    (by simpa) (by simpa) (by simpa) (by simpa) (by simpa) (by simpa)
  rw [lpGhost_ursell4_eq,
    lpGhost_twoPoint_eq, lpGhost_twoPoint_eq, lpGhost_twoPoint_eq] at hlead
  exact hlead


theorem lpField_graham_four_point_strong
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall x, 0 <= hf x)
    (i j k l : V) :
    2 * expJ G.edgeFinset J hf (fun s => spin s k * spin s l) *
        (expJ G.edgeFinset J hf (fun s => spin s i * spin s k) -
          expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) *
        (expJ G.edgeFinset J hf (fun s => spin s j * spin s k) -
          expJ G.edgeFinset J hf (fun s => spin s j * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s k * spin s l)) <=
      (1 - expJ G.edgeFinset J hf (fun s => spin s k * spin s l) ^ 2) *
        (-(lpFieldUrsell4 G J hf i j k l +
          2 * (expJ G.edgeFinset J hf (fun s => spin s i * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s j * spin s l) *
            expJ G.edgeFinset J hf (fun s => spin s k * spin s l)))) := by
  have h := grahamMarkedSite_four_point_strong (withGhost G)
    (lpGhostCoupling J hf) (lpGhostCoupling_nonneg J hf hJ hhf)
    (some i) (some j) (some k) (some l)
  rw [lpGhost_ursell4_eq] at h
  unfold grahamBridgeGap at h
  simp only [lpGhost_twoPoint_eq] at h
  simpa [mul_comm] using h

end
end StatMech.Ising
