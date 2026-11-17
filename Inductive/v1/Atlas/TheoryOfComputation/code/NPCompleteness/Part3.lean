/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Nodup
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
public import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part3

namespace CookLevin

open TuringMachine NPCompleteness

/-- States of the trivial NTM that decides `ThreeSATLang` by guessing a satisfying
assignment in one nondeterministic step. -/
public inductive ThreeSATState
  | start
  | accept
  | reject
  deriving DecidableEq

end CookLevin
