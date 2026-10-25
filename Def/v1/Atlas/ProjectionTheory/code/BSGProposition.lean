/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BSGProposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Pointwise Finset


namespace BSG

variable {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]

/-- The sumset image of a finite set $X \subseteq G \times G$ under addition: $\{a + b : (a,b) \in X\}$. -/
noncomputable def sumsetImage (X : Finset (G × G)) : Finset G :=
  X.image (fun p => p.1 + p.2)

end BSG
