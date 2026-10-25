/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.SteinerTriple
open MeasureTheory Filter Topology Real Set


noncomputable section

/-- Finiteness of the type of Steiner triple systems on $\{0,\dots,n-1\}$. -/
instance (n : ℕ) : Empty.Finite (SteinerTripleSystem (Fin n)) :=
  Empty.Finite.of_injective (fun s => s.triples) (fun s1 s2 h => by cases s1; cases s2; congr)

end
