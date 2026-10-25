/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part4
import Lemma.Set.IsHomothetic_πLattice
import Lemma.Set.ConjSet.eq.Image
import Structure.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Topology.Algebra.Group.Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- Topological hypotheses on the fraction field $k$ of a complete DVR: the valuation
ring $\mathfrak{o}$ is open and compact in $k$, its maximal ideal is open, $k$ is a
$T_1$ topological ring. This is the package of assumptions needed to make the
Iwahori subgroup compact-open in $SL_V(k)$. -/
class DVRTopologicalAssumptions (C : DVRContext) [TopologicalSpace C.k] : Prop where
  isOpen_valRing : IsOpen {x : C.k | C.isInO x}
  isOpen_maxIdeal : IsOpen {x : C.k | C.isInMaxIdeal x}
  isTopologicalRing : IsTopologicalRing C.k
  isCompact_valRing : IsCompact {x : C.k | C.isInO x}
  t1Space : T1Space C.k


end AffineBuildingSLVStrong
