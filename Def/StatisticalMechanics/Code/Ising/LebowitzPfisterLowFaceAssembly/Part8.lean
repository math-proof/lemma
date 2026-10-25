/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part7
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def quadraticAverage (x : Real) (f : Fin 8 -> Real) : Real :=
  f 0 + 7 * x * (f 1 - f 0) +
    21 * x ^ 2 * (f 2 - 2 * f 1 + f 0)

end LowFaceCertificate
end
end StatMech.Ising
