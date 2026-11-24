module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part6
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def bernsteinAverageSeven (x : Real) (f : Fin 8 -> Real) : Real :=
  ∑ i : Fin 8, bernsteinWeight 7 i x * f i

end LowFaceCertificate
end
end StatMech.Ising
