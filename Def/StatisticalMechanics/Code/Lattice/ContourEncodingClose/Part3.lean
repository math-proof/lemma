module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part2
open Set Finset SimpleGraph
open StatMech.Ising


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def ccb_AnchoredBoundaryWalkExists (n ℓ : ℕ) : Prop :=
  ∃ D : (Σ v : Site 2, (hypercubicLattice 2).Walk v v) → Finset (Sym2 (Site 2)),
    ∀ K ∈ ccb_contourFiber 2 n ℓ,
      ∃ v ∈ ccb_anchorRow ℓ, ∃ w : (hypercubicLattice 2).Walk v v,
        w.length = ℓ ∧ D ⟨v, w⟩ = crossEdges (↑K) (bondFinsetTouch 2 n)


end Lattice
end StatMech
