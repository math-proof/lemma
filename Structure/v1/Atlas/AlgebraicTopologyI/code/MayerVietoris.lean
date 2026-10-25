/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
open Set Topology EilenbergSteenrod Function

universe u


namespace MayerVietoris

/-- A Mayer-Vietoris cover of a space: a two-element family `{A, B}` of subsets of `X`
whose interiors cover `X`. This is the input data for Theorem 11.5. -/
structure MayerVietorisCover where
  X : Type u
  instTop : TopologicalSpace X
  A : Set X
  B : Set X
  cover : interior A ∪ interior B = univ

end MayerVietoris
