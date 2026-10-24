/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsTheoremProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
import Lemma.List.All.of.All.IsChain.Ne
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Folding
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes
import Mathlib.GroupTheory.Coxeter.Length

open ChamberComplex AptIsCoxeterProof

variable {V : Type*} [DecidableEq V]

namespace TitsTheoremProof

/-- The gallery path realizing the word $s_{i_1} \dots s_{i_n}$ starting from
$w$: the list $[w, w s_{i_1}, w s_{i_1} s_{i_2}, \dots]$. -/
def galleryPath {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (w : M.Group) : List B → List M.Group
  | [] => [w]
  | i :: rest => w :: galleryPath M (w * M.toCoxeterSystem.simple i) rest

/-- Accumulated word product: starting from $w$, multiply right by each
simple generator $s_i$ in the word. -/
def wordProduct {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (w : M.Group) : List B → M.Group
  | [] => w
  | i :: rest => wordProduct M (w * M.toCoxeterSystem.simple i) rest
