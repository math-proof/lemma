/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionFactor
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)


noncomputable def isingCoordinateDomainHalfWeight
    (beta : Real)
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower : ConfigSpace (IsingCoordinateDomainLower K i m)) : Real :=
  Real.exp (-(beta / 2) * hamiltonian (freeDomainGraph K) 0
    (isingCoordinateDomainGlue K i m hK boundary lower lower))

end
end StatMech.FrontierA
