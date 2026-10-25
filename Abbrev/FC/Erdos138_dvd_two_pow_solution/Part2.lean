/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos138_dvd_two_pow_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.Erdos138_dvd_two_pow_solution.Part2
open Nat Filter


namespace Erdos138

abbrev BinaryGaloisField (p : ℕ) := GaloisField 2 p

end Erdos138
