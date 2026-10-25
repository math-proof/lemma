/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PBWLieSubmodBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.RingTheory.SimpleModule.Basic


noncomputable section

section AlgHomExt

variable {R : Type*} [CommRing R]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

def LieSubmodule.preservingSubalgebra (N : LieSubmodule R L M) :
    Subalgebra R (UniversalEnvelopingAlgebra R L) where
  carrier := {u | ∀ m ∈ N, u • m ∈ N}
  mul_mem' {a b} ha hb m hm := by rw [mul_smul]; exact ha _ (hb _ hm)
  one_mem' m hm := by simp [hm]
  add_mem' {a b} ha hb m hm := by rw [add_smul]; exact N.add_mem (ha _ hm) (hb _ hm)
  zero_mem' m hm := by simp [N.zero_mem]
  algebraMap_mem' r m hm := by rw [algebraMap_smul]; exact N.smul_mem r hm

set_option linter.unusedSectionVars false in

def LieSubmodule.toUEASubmodule
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : LieSubmodule R L M) : Submodule (UniversalEnvelopingAlgebra R L) M where
  carrier := N.carrier
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' u m hm := by
    have hu : u ∈ N.preservingSubalgebra :=
      (N.preservingSubalgebra_eq_top hcompat) ▸ trivial
    exact hu m hm

def LieSubmodule.ofUEASubmodule'
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : Submodule (UniversalEnvelopingAlgebra R L) M) : LieSubmodule R L M where
  carrier := N.carrier
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' r m hm := by
    have h : (algebraMap R (UniversalEnvelopingAlgebra R L) r) • m ∈ N :=
      N.smul_mem (algebraMap R (UniversalEnvelopingAlgebra R L) r) hm
    rwa [algebraMap_smul] at h
  lie_mem {x m} hm := by
    rw [hcompat x m]
    exact N.smul_mem _ hm

end AlgHomExt
end
