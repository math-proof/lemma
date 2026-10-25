/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterFoldingHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
import Lemma.List.All.of.All.IsChain.Ne
import Lemma.Nat.NotChamberAdjacent
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
import Mathlib.GroupTheory.Coxeter.Length
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

section GroupLevel

variable {B_idx : Type*} (M : CoxeterMatrix B_idx)

/-- The group-level half-apartment map for simple reflection $s_i$: returns $w$ if multiplication
by $s_i$ on the left lengthens $w$, and $s_i w$ otherwise. -/
noncomputable def coxeterHalfGroupMap (i : B_idx) (w : M.Group) : M.Group :=
  let cs := M.toCoxeterSystem
  if cs.length (cs.simple i * w) > cs.length w then w
  else cs.simple i * w

/-- Lift `coxeterHalfGroupMap` from the Coxeter group to the chamber complex along a labelling
$\varphi$: maps chamber $E$ to a chamber whose $\varphi$-image equals the half-apartment image of
$\varphi(E)$. -/
noncomputable def coxeterHalfChamberMap
    (K : ChamberComplex V)
    (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
    (i : B_idx) (E : Finset V) : Finset V :=
  let cs := M.toCoxeterSystem
  let w := φ E
  if cs.length (cs.simple i * w) > cs.length w then E
  else (hsurj (cs.simple i * w)).choose

end GroupLevel
end ChamberComplex
