/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section K4Recovery

def k4Missing (a b : Fin 4) : List (Fin 4) :=
  ([0, 1, 2, 3] : List (Fin 4)).filter (fun k => k ≠ a ∧ k ≠ b)


def k4CompPair (a b : Fin 4) : Sym2 (Fin 4) :=
  match k4Missing a b with
  | [c, d] => s(c, d)
  | _ => s(a, b)


def k4Comp (e : Sym2 (Fin 4)) : Sym2 (Fin 4) :=
  Sym2.lift ⟨k4CompPair, by decide⟩ e


end K4Recovery
end Ising
end StatMech
