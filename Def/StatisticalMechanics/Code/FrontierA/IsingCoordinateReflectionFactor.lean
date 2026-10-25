/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)


noncomputable def isingCoordinateDomainCrossBoundary :
    Finset (IsingCoordinateDomainLower K i m) :=
  Finset.univ.filter fun z =>
    (freeDomainGraph K).Adj z.1
      (isingCoordinateDomainReflectEquiv K i m hK z.1)

def isingCoordinateDomainCrossEdge
    (z : IsingCoordinateDomainLower K i m) :
    Sym2 (freeDomainVertices K) :=
  s(z.1, isingCoordinateDomainReflectEquiv K i m hK z.1)

end
end StatMech.FrontierA
