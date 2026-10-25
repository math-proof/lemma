/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Revealment.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part3
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace RevealmentConstruction

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem connOpenSet_of_mem {endU endV : E → V} {ω : ConfigSpace E} {x : V} {B : Set V}
    (hx : x ∈ B) : ConnOpenSet endU endV ω x B :=
  ⟨x, hx, ReachOpen.refl x⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem connOpenSet_prop {endU endV : E → V} {ω : ConfigSpace E} {B : Set V} {e : E}
    (hopen : ω e = true) (hU : ConnOpenSet endU endV ω (endU e) B) :
    ConnOpenSet endU endV ω (endV e) B := by
  obtain ⟨b, hbB, hreach⟩ := hU
  exact ⟨b, hbB, ReachOpen.step e hopen (Or.inr ⟨rfl, rfl⟩) hreach⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem connOpenSet_prop' {endU endV : E → V} {ω : ConfigSpace E} {B : Set V} {e : E}
    (hopen : ω e = true) (hV : ConnOpenSet endU endV ω (endV e) B) :
    ConnOpenSet endU endV ω (endU e) B := by
  obtain ⟨b, hbB, hreach⟩ := hV
  exact ⟨b, hbB, ReachOpen.step e hopen (Or.inl ⟨rfl, rfl⟩) hreach⟩


end RevealmentConstruction
end OSSS
end StatMech
