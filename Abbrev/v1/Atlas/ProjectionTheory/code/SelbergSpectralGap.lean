/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergSpectralGap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open scoped Matrix BigOperators


namespace SelbergSpectralGap

/-- The group $\mathrm{SL}_2(\mathbb{F}_p)$ of $2 \times 2$ matrices with determinant $1$
over the finite field $\mathbb{Z}/p\mathbb{Z}$. -/
abbrev SL2p (p : ℕ) [Fact (Nat.Prime p)] := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)

end SelbergSpectralGap
