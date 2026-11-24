module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part3
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


noncomputable def flankFacesSym : Sym2 (Site 2) → Sym2 (Site 2) :=
  Sym2.lift ⟨flankFaces, flankFaces_comm⟩

end Lattice
end StatMech
