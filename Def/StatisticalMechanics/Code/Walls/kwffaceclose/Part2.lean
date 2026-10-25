/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Walls.jcwcutsetwalk
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Theorem.StatisticalMechanics.Code.Walls.kwffaceclose
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


noncomputable def kwf_faceParity (T : Site 2 → Prop) :
    {x y : Site 2} → (hypercubicLattice 2).Walk x y → Bool
  | _, _, .nil => false
  | _, _, .cons (u := u) (v := v) _ p =>
      (decide (s(u, v) ∈ jed_cutSet T)).xor (kwf_faceParity T p)


def kwf_FaceCutLinkingParity : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
    ∀ (x : Site 2) (p : (hypercubicLattice 2).Walk x x),
      kwf_faceParity (fwr_faceInside Vc) p = false


end Walls
end StatMech
