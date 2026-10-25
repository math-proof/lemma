/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.UnitInterval
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section15
open Topology


namespace CWSubcomplex

variable {X : Type*} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]

/-- A subcomplex `E` is *finite* if, with its induced CW-structure, it has only
finitely many cells in total. -/
def IsFinite [T2Space X] (E : CWSubcomplex X) : Prop :=
  haveI := E.instRelCWComplex
  Topology.RelCWComplex.Finite (E : Set X)

end CWSubcomplex
