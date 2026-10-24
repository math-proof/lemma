/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators


namespace BooleanFourier

def IsDictator {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ i : Fin n, ∀ x, f x = x i

def IsUnanimous {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  f (fun _ => true) = true ∧ f (fun _ => false) = false

def prefersOver {m : ℕ} (ranking : Equiv.Perm (Fin m)) (a b : Fin m) : Bool :=
  decide (ranking a < ranking b)

def IsArrowViable {n : ℕ} (f : (Fin n → Bool) → Bool) (m : ℕ) : Prop :=
  ∀ (rankings : Fin n → Equiv.Perm (Fin m)),
    ∀ (a b c : Fin m),
      a ≠ b → b ≠ c → a ≠ c →
      f (fun i => prefersOver (rankings i) a b) = true →
      f (fun i => prefersOver (rankings i) b c) = true →
      f (fun i => prefersOver (rankings i) a c) = true

def IsOdd {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f (fun i => !(x i)) = !(f x)

private def flipCoord {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

noncomputable def influence {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) / (2 ^ n : ℝ)
end BooleanFourier
