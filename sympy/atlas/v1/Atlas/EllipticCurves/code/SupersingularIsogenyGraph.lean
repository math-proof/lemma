/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/SupersingularIsogenyGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.IsogenyVolcano
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyVolcano
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Supersingular
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Polynomial Finset

namespace SupersingularIsogenyGraph

/-- The type of supersingular `j`-invariants over the algebraic closure of `𝔽_p`.
These are the `j`-invariants of supersingular elliptic curves in characteristic `p`,
all of which lie in `𝔽_{p^2}` (Theorem 13.16). -/
end SupersingularIsogenyGraph
