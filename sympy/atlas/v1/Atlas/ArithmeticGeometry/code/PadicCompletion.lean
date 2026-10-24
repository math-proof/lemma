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

universe u

/-- The inverse limit of a sequence of types $S_0, S_1, \ldots$ connected by transition maps
$f_n : S_{n+1} \to S_n$: a coherent sequence $(s_n)_{n \in \mathbb{N}}$ with $s_n \in S_n$ and
$f_n(s_{n+1}) = s_n$ for every $n$. -/
def InverseLimit (S : ℕ → Type u) (f : (n : ℕ) → S (n + 1) → S n) : Type u :=
  { s : (n : ℕ) → S n // ∀ n, f n (s (n + 1)) = s n }

namespace InverseLimit

variable {S : ℕ → Type u} (fn : (n : ℕ) → S (n + 1) → S n)

/-- The $k$-fold image chain `imgCh fn n k`: the subset of $S_n$ obtained by iterating the
transition maps $k$ times starting from $S_{n+k}$. Forms an antitone family in $k$ that captures
which elements of $S_n$ lift back through the inverse system. -/
def imgCh : (n k : ℕ) → Set (S n)
  | _, 0 => Set.univ
  | n, k + 1 => fn n '' (imgCh (n + 1) k)

/-- The finite set of roots of $f \in \mathbb{Z}_p[X]$ in the quotient ring
$\mathbb{Z}/p^n\mathbb{Z}$, i.e. roots of the reduction of $f$ modulo $p^n$. -/
def PolyRootSet (f : Polynomial ℤ_[p]) (n : ℕ) : Type :=
  {r : ZMod (p ^ n) // Polynomial.eval r (Polynomial.map (toZModPow n) f) = 0}

/-- `PolyRootSet f n` is a finite type, being a subtype of the finite ring
$\mathbb{Z}/p^n\mathbb{Z}$. -/
instance polyRootSetFintype (f : Polynomial ℤ_[p]) (n : ℕ) :
    Fintype (PolyRootSet f n) :=
  Subtype.fintype _

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
