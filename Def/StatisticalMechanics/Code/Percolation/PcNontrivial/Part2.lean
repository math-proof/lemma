/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part2
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal
open Finset

set_option linter.deprecated false
set_option linter.style.longLine false


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def edgeOf (g : ℕ → Fin d × Bool) (k : ℕ) : Sym2 (Site d) :=
  s(vertOf g k, vertOf g (k + 1))


def wordEvent (g : ℕ → Fin d × Bool) (n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∀ k ∈ Finset.range n, ω (edgeOf g k) = true}


def goodWord (g : ℕ → Fin d × Bool) (n : ℕ) : Prop :=
  Set.InjOn (vertOf g) (Finset.range (n + 1))


end Percolation
end StatMech
