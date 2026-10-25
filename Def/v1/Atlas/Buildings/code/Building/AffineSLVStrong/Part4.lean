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
import Abbrev.v1.Atlas.Buildings.code.Building.AffineSLVStrong
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- The $(i,j)$-th matrix entry of an element of $SL_n(k)$, as a function $SL_n(k)
\to k$. -/
def matEntryProj (C : DVRContext) (i j : Fin C.n) : SLV C → C.k :=
  fun g => (g : Matrix (Fin C.n) (Fin C.n) C.k) i j

/-- The Iwahori condition on the $(i,j)$-entry: lies in the maximal ideal
$\mathfrak{m}$ if $i > j$ (strictly below the diagonal) and in $\mathfrak{o}$
otherwise. -/
def iwahoriEntryCondition (C : DVRContext) (i j : Fin C.n) : Set C.k :=
  if i.val > j.val then {x | C.isInMaxIdeal x} else {x | C.isInO x}

/-- The Iwahori subset of $SL_n(k)$: matrices in $SL_n(\mathfrak{o})$ whose
reduction modulo $\mathfrak{m}$ is upper-triangular. -/
def IwahoriSetSLV (C : DVRContext) : Set (SLV C) :=
  ⋂ (i : Fin C.n), ⋂ (j : Fin C.n),
    matEntryProj C i j ⁻¹' iwahoriEntryCondition C i j


end AffineBuildingSLVStrong
