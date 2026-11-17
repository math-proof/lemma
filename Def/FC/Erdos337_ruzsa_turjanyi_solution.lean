/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib

@[expose] public section

namespace Erdos337

open Filter Set Asymptotics

open scoped Pointwise

noncomputable def trunc (A : Set ℕ) (N : ℕ) : Finset ℤ :=
  (A ∩ Icc 0 N).toFinite.toFinset.image (fun n : ℕ => (n : ℤ))

end Erdos337
