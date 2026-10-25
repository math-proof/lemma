/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.PascalCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PascalCurves
open Polynomial

set_option autoImplicit false


namespace ProjectivePascal

/-- A projective conic on P^2: a function on k^3 that is homogeneous of degree 2. -/
structure Conic (k : Type*) [Field k] where
  eval : (Fin 3 → k) → k
  homog : ∀ (c : k) (v : Fin 3 → k), eval (c • v) = c ^ 2 * eval v

/-- A projective line on P^2: a k-linear function k^3 → k. -/
structure Line (k : Type*) [Field k] where
  eval : (Fin 3 → k) → k
  map_add : ∀ (v w : Fin 3 → k), eval (v + w) = eval v + eval w
  map_smul : ∀ (c : k) (v : Fin 3 → k), eval (c • v) = c * eval v

end ProjectivePascal
