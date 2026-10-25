/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IntegerFactorization
import Inductive.v1.Atlas.EllipticCurves.code.ECM


noncomputable section

open Nat Finset

/-- `ECMResult.isSuccess` is `True` exactly when the result is a factor, `False` on failure. -/
def ECMResult.isSuccess {N : ℕ} : ECMResult N → Prop
  | ECMResult.factor _ _ _ _ => True
  | ECMResult.failure => False

end
