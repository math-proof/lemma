/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

def oddPrismSurfaceLow (n r : Nat) :
    Finset (Fin (2 * n + 1)) :=
  Finset.univ.filter fun i => i.val < r

def oddPrismSurfaceHigh (n r : Nat) :
    Finset (Fin (2 * n + 1)) :=
  Finset.univ.filter fun i => 2 * n < i.val + r

def oddPrismSurfaceBoundaryPairs (n r : Nat) :
    Finset (Fin (2 * n + 1) × Fin (2 * n + 1)) :=
  let U : Finset (Fin (2 * n + 1)) := Finset.univ
  oddPrismSurfaceLow n r ×ˢ U ∪
    oddPrismSurfaceHigh n r ×ˢ U ∪
    U ×ˢ oddPrismSurfaceLow n r ∪
    U ×ˢ oddPrismSurfaceHigh n r

def oddPrismSurfaceInterior (n r : Nat)
    (q : Fin (2 * n + 1) × Fin (2 * n + 1)) : Prop :=
  r <= q.1.val ∧ q.1.val + r <= 2 * n ∧
    r <= q.2.val ∧ q.2.val + r <= 2 * n

noncomputable def oddPrismSurfaceNonInterior (n r : Nat) :
    Finset (Fin (2 * n + 1) × Fin (2 * n + 1)) :=
  by
    classical
    exact Finset.univ.filter fun q => ¬ oddPrismSurfaceInterior n r q

end
end StatMech.FrontierA
