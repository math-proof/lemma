/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part5
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def crossNumerator (x y z a b c : Real) : Real :=
  y * z * (x - x ^ 3 + y - y ^ 3 + z - z ^ 3) +
    9 * x * y * z * (x + y) * (1 - y) * a +
    9 * x * y * z * (x + z) * (1 - z) * b +
    9 * y ^ 2 * z * (y + z) * (1 - z) * c -
    3 * x * y * z * (3 - 2 * x) * (1 - y) * (1 - z) * (a * b) +
    6 * x ^ 2 * z * (1 - y) ^ 2 * (1 - z) * (a ^ 2 * b) +
    6 * x ^ 2 * y * (1 - y) * (1 - z) ^ 2 * (a * b ^ 2) -
    3 * x * y * z * (3 - 2 * y) * (1 - y) * (1 - z) * (a * c) +
    6 * x * y * z * (1 - y) ^ 2 * (1 - z) * (a ^ 2 * c) +
    6 * x * y ^ 2 * (1 - y) * (1 - z) ^ 2 * (a * c ^ 2) -
    3 * x * y ^ 2 * (3 - 2 * z) * (1 - z) ^ 2 * (b * c) +
    6 * x * y ^ 2 * (1 - z) ^ 3 * (b ^ 2 * c) +
    6 * x * y ^ 2 * (1 - z) ^ 3 * (b * c ^ 2)

end LowFaceCertificate
end
end StatMech.Ising
