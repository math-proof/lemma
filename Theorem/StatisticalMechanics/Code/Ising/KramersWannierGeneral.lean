/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Def.StatisticalMechanics.Code.Ising.KramersWannierGeneral
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Handshake

variable {V : Type*} (Gp : SimpleGraph V) (s : ConfigSpace V)


theorem walkDis_parity {x y : V} (p : Gp.Walk x y) :
    walkDis Gp s p % 2 = (if s x ≠ s y then 1 else 0) := by
  induction p with
  | nil => simp [walkDis]
  | @cons u v w h q ih =>
    simp only [walkDis]
    rw [Nat.add_mod, ih]
    cases hu : s u <;> cases hv : s v <;> cases hw : s w <;> simp_all


theorem walkDis_closed_even {x : V} (p : Gp.Walk x x) :
    walkDis Gp s p % 2 = 0 := by
  rw [walkDis_parity]; simp


theorem walkDis_eq_darts_sum {x y : V} (p : Gp.Walk x y) :
    walkDis Gp s p
      = (p.darts.map (fun d => if s d.fst ≠ s d.snd then 1 else 0)).sum := by
  induction p with
  | nil => simp [walkDis]
  | @cons u v w h q ih =>
    simp only [walkDis, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]

end Handshake
end Ising
end StatMech
