/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
open Polynomial PadicInt HilbertSymbol


noncomputable section

/-- For $n \geq 1$, an element of $\mathbb{Z}_p$ is a unit iff its reduction mod $p^n$
is a unit. -/
lemma PadicInt.isUnit_toZModPow_iff {p : ℕ} [hp : Fact (Nat.Prime p)]
    {n : ℕ} (hn : 0 < n) {x : ℤ_[p]} :
    IsUnit (toZModPow n x) ↔ IsUnit x := by
  constructor
  · intro h
    rw [isUnit_iff]
    by_contra hne
    have hlt : ‖x‖ < 1 := lt_of_le_of_ne (norm_le_one x) hne
    rw [PadicInt.norm_lt_one_iff_dvd] at hlt
    have h1 : toZModPow 1 x = 0 := by
      rw [← RingHom.mem_ker, ker_toZModPow, Ideal.mem_span_singleton, pow_one]
      exact hlt
    have hcomp := congr_fun (congr_arg DFunLike.coe (zmod_cast_comp_toZModPow 1 n hn)) x
    simp only [RingHom.comp_apply] at hcomp
    rw [h1] at hcomp
    have hu : IsUnit ((ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 1))) (toZModPow n x)) :=
      h.map _
    rw [hcomp] at hu
    haveI : Nontrivial (ZMod (p ^ 1)) := by
      rw [show p ^ 1 = p from pow_one p]
      haveI : NeZero p := ⟨hp.out.ne_zero⟩
      infer_instance
    exact not_isUnit_zero hu
  · exact fun h => h.map (toZModPow n)

end
