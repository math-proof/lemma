module
public import Def.v1.Atlas.Buildings.code.Building.TitsTheoremProof
public import Theorem.Finset.Any_And_EqImageToFunMorph.of.AdjacentToSimplicialComplex.HasSufficientFoldings
public import Theorem.Finset.Adjacent
public import Theorem.Finset.AgreeOnImage.of.AgreeOn
public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
public import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
open ChamberComplex AptIsCoxeterProof


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/WallReflectionAction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {V : Type*} [DecidableEq V]


namespace WallReflectionAction

/-- Apply a word of vertex maps (e.g. wall reflections) sequentially to a
chamber $C$, taking images at each step. -/
def applyFunWord (word : List (V → V)) (C : Finset V) : Finset V :=
  word.foldl (fun D f => D.image f) C

end WallReflectionAction
