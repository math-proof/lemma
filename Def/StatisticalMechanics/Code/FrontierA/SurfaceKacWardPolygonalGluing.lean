/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


noncomputable def surfaceWalkPrefixHomology {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (m : Nat) : SurfaceHomology g :=
  ((p.edges.take m).map edgeClass).sum


noncomputable def surfaceWalkQuadraticHeight {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (m : Nat) : Int :=
  (surfaceBaseQuadraticParity
    (surfaceWalkPrefixHomology edgeClass p m)).val


noncomputable def surfaceWalkQuadraticIncrement {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (k : Fin p.darts.length) : Int :=
  surfaceWalkQuadraticHeight edgeClass p (k.val + 1) -
    surfaceWalkQuadraticHeight edgeClass p k.val

end StatMech.FrontierA
