/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def boxVerts (n : ℕ) : Finset (Site 2) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)).image
    (fun p => ![p.1, p.2])


noncomputable def hEdges (n : ℕ) : Finset (Sym2 (Site 2)) :=
  (Finset.Ico (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)).image
    (fun p => s(![p.1, p.2], ![p.1 + 1, p.2]))


noncomputable def vEdges (n : ℕ) : Finset (Sym2 (Site 2)) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Ico (-(n : ℤ)) (n : ℤ)).image
    (fun p => s(![p.1, p.2], ![p.1, p.2 + 1]))


noncomputable def boxEdges (n : ℕ) : Finset (Sym2 (Site 2)) := hEdges n ∪ vEdges n


noncomputable def boxCells (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Ico (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Ico (-(n : ℤ)) (n : ℤ)


end Lattice
end StatMech
