/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part7
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma bernsteinAverageSeven_const (x q : Real) :
    bernsteinAverageSeven x (fun _ => q) = q := by
  unfold bernsteinAverageSeven
  have h := scaledBernFactor_sum_seven 0 (by norm_num) x
  norm_num [scaledBernFactor, Nat.choose] at h
  calc
    bernsteinAverageSeven x (fun _ => q) =
        q / 105 * (∑ i : Fin 8, 105 * bernsteinWeight 7 i x) := by
      unfold bernsteinAverageSeven
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = q := by rw [h]; ring

lemma bernsteinAverageSeven_add (x : Real) (f g : Fin 8 -> Real) :
    bernsteinAverageSeven x (fun i => f i + g i) =
      bernsteinAverageSeven x f + bernsteinAverageSeven x g := by
  unfold bernsteinAverageSeven
  simp only [mul_add, Finset.sum_add_distrib]

lemma bernsteinAverageSeven_natCast_mul (x q : Real) :
    bernsteinAverageSeven x (fun i => q * i.val) = q * (7 * x) := by
  unfold bernsteinAverageSeven
  have h := scaledBernFactor_sum_seven 1 (by norm_num) x
  norm_num [scaledBernFactor, Nat.choose] at h
  calc
    bernsteinAverageSeven x (fun i => q * i.val) =
        q / 15 * (∑ i : Fin 8, (i.val : Real) * 15 * bernsteinWeight 7 i x) := by
      unfold bernsteinAverageSeven
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = q * (7 * x) := by rw [h]; ring

lemma bernsteinAverageSeven_falling_mul (x q : Real) :
    bernsteinAverageSeven x (fun i => q * (i.val * (i.val - 1) : Nat)) =
      q * (42 * x ^ 2) := by
  unfold bernsteinAverageSeven
  have h := scaledBernFactor_sum_seven 2 (by norm_num) x
  norm_num [scaledBernFactor, Nat.choose] at h
  calc
    bernsteinAverageSeven x (fun i => q * (i.val * (i.val - 1) : Nat)) =
        (2 * q) / 5 *
          (∑ i : Fin 8, (i.val.choose 2 : Real) * 5 * bernsteinWeight 7 i x) := by
      unfold bernsteinAverageSeven
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      fin_cases i <;> norm_num [Nat.choose] <;> ring
    _ = q * (42 * x ^ 2) := by rw [h]; ring

lemma bernsteinAverageSeven_choose_two_mul (x q : Real) :
    bernsteinAverageSeven x (fun i => q * i.val.choose 2) =
      q * (21 * x ^ 2) := by
  calc
    bernsteinAverageSeven x (fun i => q * i.val.choose 2) =
        bernsteinAverageSeven x
          (fun i => (q / 2) * (i.val * (i.val - 1) : Nat)) := by
      apply congrArg (bernsteinAverageSeven x)
      funext i
      fin_cases i <;> norm_num [Nat.choose] <;> ring
    _ = (q / 2) * (42 * x ^ 2) :=
      bernsteinAverageSeven_falling_mul x (q / 2)
    _ = q * (21 * x ^ 2) := by ring

end LowFaceCertificate
end
end StatMech.Ising
