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
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part4
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


def geomGuard (endU endV : E → V) (disc : Finset V) (e : E) : Bool :=
  decide (endU e ∈ disc ∨ endV e ∈ disc)


def geomStep (endU endV : E → V) (disc : Finset V) (e : E) (b : Bool) : Finset V :=
  if b then insert (endU e) (insert (endV e) disc) else disc


def geomInv (endU endV : E → V) (ω : ConfigSpace E) (B : Set V) (disc : Finset V) : Prop :=
  ∀ x ∈ disc, ConnOpenSet endU endV ω x B

end RevealmentConstruction
end OSSS
end StatMech
