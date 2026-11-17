/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupHomomorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib

@[expose] public section

namespace GroupHomomorphisms

variable {G G' : Type*} [Group G] [Group G']

def GroupHomomorphism (G G' : Type*) [Group G] [Group G'] := G →* G'

end GroupHomomorphisms
