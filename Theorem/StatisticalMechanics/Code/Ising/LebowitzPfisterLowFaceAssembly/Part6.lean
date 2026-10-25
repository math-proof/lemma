/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part6
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma eval_crossCoeffPoly (i j k : Nat) (x y z : Real) :
    (crossCoeffPoly i j k).eval x y z =
      1764 * y * z * (x - x ^ 3 + y - y ^ 3 + z - z ^ 3) +
      (252 * i : Int) * (9 * x * y * z * (x + y) * (1 - y)) +
      (252 * j : Int) * (9 * x * y * z * (x + z) * (1 - z)) +
      (252 * k : Int) * (9 * y ^ 2 * z * (y + z) * (1 - z)) -
      (36 * i * j : Int) *
        (3 * x * y * z * (3 - 2 * x) * (1 - y) * (1 - z)) +
      (6 * i * (i - 1) * j : Int) *
        (6 * x ^ 2 * z * (1 - y) ^ 2 * (1 - z)) +
      (6 * j * (j - 1) * i : Int) *
        (6 * x ^ 2 * y * (1 - y) * (1 - z) ^ 2) -
      (36 * i * k : Int) *
        (3 * x * y * z * (3 - 2 * y) * (1 - y) * (1 - z)) +
      (6 * i * (i - 1) * k : Int) *
        (6 * x * y * z * (1 - y) ^ 2 * (1 - z)) +
      (6 * k * (k - 1) * i : Int) *
        (6 * x * y ^ 2 * (1 - y) * (1 - z) ^ 2) -
      (36 * j * k : Int) *
        (3 * x * y ^ 2 * (3 - 2 * z) * (1 - z) ^ 2) +
      (6 * j * (j - 1) * k : Int) * (6 * x * y ^ 2 * (1 - z) ^ 3) +
      (6 * k * (k - 1) * j : Int) * (6 * x * y ^ 2 * (1 - z) ^ 3) := by
  simp only [crossCoeffPoly]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_const,
    eval_zero, eval_one, eval_two, eval_three, eval_six, eval_nine, eval_1764]
  norm_num [vx, vy, vz, TriPoly.eval, evalTerms, TriTerm.eval]

end LowFaceCertificate
end
end StatMech.Ising
