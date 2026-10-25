/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part7
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


theorem isClopen_walkOpenEvent {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    IsClopen (walkOpenEvent p) := by
  have heq : walkOpenEvent p =
      ⋂ e ∈ (p.edges.toFinset : Set (Sym2 V)),
        {omega : ConfigSpace (Sym2 V) | omega e = true} := by
    ext omega
    simp [walkOpenEvent]
  rw [heq]
  have hsingle : ∀ e : Sym2 V,
      IsClopen {omega : ConfigSpace (Sym2 V) | omega e = true} := by
    intro e
    change IsClopen ((fun omega : ConfigSpace (Sym2 V) => omega e) ⁻¹' {true})
    exact IsClopen.preimage (isClopen_discrete _)
      (StatMech.ConfigSpace.continuous_eval e)
  exact Set.Finite.isClopen_biInter p.edges.toFinset.finite_toSet
    (fun e _ => hsingle e)

theorem isIncreasing_walkOpenEvent {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    IsIncreasing (walkOpenEvent p) := by
  intro omega eta home hopen e he
  have hle := home e
  rw [hopen e he] at hle
  exact le_antisymm le_top hle


end StatMech.FK.PeriodicPlanar
