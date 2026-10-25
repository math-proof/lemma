/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Exact
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Prod
open Set Topology

universe u


namespace EilenbergSteenrod

/-- A pair of topological spaces `(X, A)`: a space `X` (the carrier `space` with topology
`instTop`) together with a subset `A ⊆ X` (called `sub`). Pairs of spaces are the objects of
the category `Top₂` on which a homology theory is defined. -/
structure TopPair where
  space : Type u
  instTop : TopologicalSpace space
  sub : Set space

end EilenbergSteenrod
