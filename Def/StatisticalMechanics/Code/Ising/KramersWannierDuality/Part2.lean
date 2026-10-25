/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section Computable

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def edgeDiff (s : ConfigSpace V) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun x y => s x != s y, fun _ _ => by simp [bne_comm]⟩ e


def cutEdgesB (s : ConfigSpace V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => edgeDiff s e)

end Computable
end Ising
end StatMech
