/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA22030_conjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA22030_conjecture


namespace OeisA22030

def err (n : ℕ) : ℤ :=
  if n < 2 then 0 else (b (n - 1) : ℤ) ^ 2 - b (n - 2) * b n


def e (k : ℕ) : ℤ := (-1 : ℤ) ^ k * err (k + 2)

end OeisA22030
