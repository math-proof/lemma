/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos138_dvd_two_pow_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.FC.Erdos138_dvd_two_pow_solution
open Nat Filter


namespace Erdos138

def erdos_138_variants_dvd_two_pow_statement : Prop := atTop.Tendsto (fun k => ((W k : ℚ)/ (2 ^ k))) atTop

end Erdos138
