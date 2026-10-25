/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open DVRContext

variable (p : ℕ) [Fact (Nat.Prime p)]


noncomputable section

set_option maxHeartbeats 32000000

/-- *A non-identity permutation moves some index upward*: for any permutation $σ \ne 1$ on
$\text{Fin}\,m$, there is some $i$ with $i < σ(i)$. Used to detect off-diagonal terms in the
Iwahori-determinant computation. Proof: if $σ(i) \le i$ for all $i$, then strict inequality
somewhere combined with $\sum σ(j) = \sum j$ gives a contradiction. -/
theorem perm_exists_gt_of_ne_one {m : ℕ} (σ : Equiv.Perm (Fin m)) (hσ : σ ≠ 1) :
    ∃ i : Fin m, i < σ i := by
  by_contra hall
  push Not at hall
  have hfix : ∀ i, σ i = i := by
    intro i
    apply le_antisymm (hall i)
    by_contra hlt; push Not at hlt
    have hsum_eq : ∑ j : Fin m, (σ j).val = ∑ j : Fin m, j.val :=
      Equiv.sum_comp σ (fun j : Fin m => j.val)
    have hsum_lt : ∑ j : Fin m, (σ j).val < ∑ j : Fin m, j.val :=
      Finset.sum_lt_sum (fun j _ => (hall j : (σ j).val ≤ j.val))
        ⟨i, Finset.mem_univ _, (hlt : (σ i).val < i.val)⟩
    linarith
  exact hσ (Equiv.ext hfix)

/-- *Product strictly less than $1$ when one factor is strictly less than $1$ and others are
$\le 1$*: pulled out as a separate fact to bound off-diagonal Iwahori products. -/
theorem prod_lt_one_of_le_one {m : ℕ} (f : Fin m → ℝ)
    (hnn : ∀ i, 0 ≤ f i) (hle : ∀ i, f i ≤ 1)
    {i₀ : Fin m} (hlt : f i₀ < 1) :
    ∏ i : Fin m, f i < 1 :=
  calc ∏ i : Fin m, f i
      = (∏ i ∈ Finset.univ.erase i₀, f i) * f i₀ := by
        rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)]; ring
    _ ≤ 1 * f i₀ := mul_le_mul_of_nonneg_right
        (Finset.prod_le_one (fun i _ => hnn i) (fun i _ => hle i)) (hnn i₀)
    _ = f i₀ := one_mul _
    _ < 1 := hlt

/-- *Ultrametric strict triangle inequality for a finite sum*: in $\mathbb{Q}_p$ (or any
ultrametric field), if every term $f(i)$ has norm $< C$, then so does the sum $\sum_i f(i)$.
Proof by induction on the finset using $\|x + y\| \le \max(\|x\|, \|y\|)$. -/
theorem ultrametric_norm_sum_lt {ι : Type*} {s : Finset ι} {f : ι → ℚ_[p]} {C : ℝ}
    (hC : 0 < C) (hbound : ∀ i ∈ s, ‖f i‖ < C) :
    ‖∑ i ∈ s, f i‖ < C := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, norm_zero]; exact hC
  | cons a s has ih =>
    rw [Finset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (hbound a (Finset.mem_cons_self a s))
        (ih (fun i hi => hbound i (Finset.mem_cons_of_mem hi))))

/-- *Iwahori determinant has $p$-adic norm $1$*: a matrix $g$ over $\mathbb{Q}_p$ that is in
Iwahori form (diagonal entries unit norm, above-diagonal $\le 1$, strictly below-diagonal
$< 1$) has $\|\det g\| = 1$. The proof expands the determinant as a sum over permutations:
the identity contributes a product of unit-norm entries giving norm $1$, while every
non-identity permutation forces at least one strictly-below-diagonal factor, making its
contribution have norm $< 1$. Ultrametricity then yields $\|\det g\| = 1$. -/
theorem iwahori_det_norm_eq_one {m : ℕ} (g : Matrix (Fin m) (Fin m) ℚ_[p])
    (hdiag : ∀ i, ‖g i i‖ = 1)
    (habove : ∀ i j, i < j → ‖g i j‖ ≤ 1)
    (hbelow : ∀ i j, j < i → ‖g i j‖ < 1) :
    ‖g.det‖ = 1 := by
  have hall_le : ∀ i j, ‖g i j‖ ≤ 1 := fun i j => by
    rcases lt_trichotomy i j with h | h | h
    · exact habove i j h
    · rw [h]; exact le_of_eq (hdiag j)
    · exact le_of_lt (hbelow i j h)
  rw [Matrix.det_apply]
  set f := fun σ : Equiv.Perm (Fin m) => Equiv.Perm.sign σ • ∏ i : Fin m, g (σ i) i
  have hid_norm : ‖f 1‖ = 1 := by
    simp only [f, Equiv.Perm.sign_one, Equiv.Perm.one_apply]
    have : (1 : ℤˣ) • (∏ x : Fin m, g x x) = ∏ x : Fin m, g x x := one_smul ℤˣ _
    rw [this, norm_prod]
    exact Finset.prod_eq_one (fun i _ => hdiag i)
  have hother : ∀ σ : Equiv.Perm (Fin m), σ ≠ 1 → ‖f σ‖ < 1 := by
    intro σ hσ
    simp only [f]
    have hsmul : ‖Equiv.Perm.sign σ • ∏ i, g (σ i) i‖ = ‖∏ i, g (σ i) i‖ := by
      rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]
    rw [hsmul, norm_prod]
    obtain ⟨i₀, hi₀⟩ := perm_exists_gt_of_ne_one σ hσ
    exact prod_lt_one_of_le_one _ (fun i => norm_nonneg _) (fun i => hall_le _ _) (hbelow _ _ hi₀)
  rw [show ∑ σ : Equiv.Perm (Fin m), f σ = f 1 + ∑ σ ∈ Finset.univ.erase 1, f σ from
    (Finset.add_sum_erase Finset.univ f (Finset.mem_univ 1)).symm]
  have hrest : ‖∑ σ ∈ Finset.univ.erase 1, f σ‖ < 1 :=
    ultrametric_norm_sum_lt p one_pos (fun σ hσ => hother σ (Finset.ne_of_mem_erase hσ))
  have hne : ‖f 1‖ ≠ ‖∑ σ ∈ Finset.univ.erase 1, f σ‖ := by
    rw [hid_norm]; exact ne_of_gt hrest
  have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hid_norm, max_eq_left (le_of_lt hrest)] at heq
  exact heq

end
