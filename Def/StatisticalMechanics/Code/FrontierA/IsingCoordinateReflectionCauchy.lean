/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionCauchy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionFactor.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionCauchy
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

noncomputable def isingCoordinateDomainHalfReflectionForm
    (beta : Real)
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) : Real :=
  ∑ lower : ConfigSpace (IsingCoordinateDomainLower K i m),
    ∑ upper : ConfigSpace (IsingCoordinateDomainLower K i m),
      (isingCoordinateDomainHalfWeight K i m hK beta boundary lower * F lower) *
        (isingCoordinateDomainHalfWeight K i m hK beta boundary upper * G upper) *
        Real.exp (beta *
          ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
            spin lower z * spin upper z)

noncomputable def isingCoordinateDomainReflectionForm
    (beta : Real)
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) : Real :=
  ∑ boundary : ConfigSpace (IsingCoordinateDomainPlane K i m),
    isingCoordinateDomainHalfReflectionForm K i m hK beta boundary F G

end
end StatMech.FrontierA
