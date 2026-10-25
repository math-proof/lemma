/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA22030_conjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace OeisA22030

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

def b (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | 3 => 249
  | n + 4 => 4 * b (n + 3) - b (n + 1) + b n

end OeisA22030
