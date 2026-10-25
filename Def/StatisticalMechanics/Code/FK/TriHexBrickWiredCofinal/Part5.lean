/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part10
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickWiredCofinal.Part4
open Filter Finset MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.OSSS

noncomputable section

def triangularBufferedBoxEvent (k : Nat)
    (A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)) :
    Set (ConfigSpace (Sym2 (triangular.BufferedVertex (2 * k)))) :=
  {rho | triangularBoxBufferedActiveRestrict k (2 * k)
      ((triangular.id_le_bufferedRadius (2 * k)))
      (restrictActive (triangular.bufferedGraph (2 * k)) rho) ∈ A}

end
end StatMech.FK.PeriodicPlanar
