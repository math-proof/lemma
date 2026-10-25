/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Instance.v1.Atlas.ArithmeticGeometry.code.PadicCompletion
universe u


namespace InverseLimit

variable {S : ℕ → Type u} (fn : (n : ℕ) → S (n + 1) → S n)

/-- Transition map from roots of $f \bmod p^{n+1}$ to roots of $f \bmod p^n$, given by reducing the
representative modulo $p^n$. Makes `(PolyRootSet f, polyRootReduction f)` into an inverse system. -/
def polyRootReduction (f : Polynomial ℤ_[p]) (n : ℕ) :
    PolyRootSet f (n + 1) → PolyRootSet f n := fun ⟨r, hr⟩ =>
  ⟨ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) r, by
    rw [eval_map] at hr ⊢
    rw [show eval₂ (toZModPow n)
          ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) r) f =
        eval₂ ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))).comp
          (toZModPow (n + 1)))
          ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) r) f
      from by rw [zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)]]
    rw [← hom_eval₂ f (toZModPow (n + 1))
        (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) r, hr, map_zero]⟩

end InverseLimit
