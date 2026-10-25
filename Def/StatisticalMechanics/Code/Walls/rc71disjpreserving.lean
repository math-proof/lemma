/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc71disjpreserving.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc70butterflymeasure.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc71_resolveMember (i : Fin n) (U : Finset (Fin n ⊕ Fin n)) : Finset (Fin n ⊕ Fin n) :=
  if Sum.inl i ∈ U ∧ Sum.inr i ∈ U then U.erase (Sum.inr i) else U


noncomputable def rc71_resolveLeft (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    Finset (Finset (Fin n ⊕ Fin n)) :=
  Fam.image (rc71_resolveMember i)


noncomputable def rc71_disjPreservingCompress (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    Finset (Finset (Fin n ⊕ Fin n)) :=
  rc71_resolveLeft i (StatMech.doubleCompress i Fam)


end StatMech.Walls
