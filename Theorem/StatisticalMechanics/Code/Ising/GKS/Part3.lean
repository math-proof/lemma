/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.GKS.Part3
open scoped BigOperators
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


omit [DecidableEq V] in
lemma IsSpinMonomial.const_one : IsSpinMonomial (fun _ : ConfigSpace V => (1 : ℝ)) :=
  ⟨0, fun s => (monomial_zero s).symm⟩

omit [DecidableEq V] in

lemma IsSpinMonomial.mul {f g : ConfigSpace V → ℝ}
    (hf : IsSpinMonomial f) (hg : IsSpinMonomial g) :
    IsSpinMonomial (fun s => f s * g s) := by
  obtain ⟨mf, hmf⟩ := hf
  obtain ⟨mg, hmg⟩ := hg
  refine ⟨mf + mg, fun s => ?_⟩
  simp only [hmf s, hmg s, monomial_add]


lemma IsSpinMonomial.sum_nonneg {f : ConfigSpace V → ℝ} (hf : IsSpinMonomial f) :
    0 ≤ ∑ s : ConfigSpace V, f s := by
  obtain ⟨m, hm⟩ := hf
  simp_rw [hm]
  exact sum_monomial_nonneg m


lemma isSpinMonomial_spin (x : V) : IsSpinMonomial (fun s => spin s x) := by
  refine ⟨Pi.single x 1, fun s => ?_⟩
  unfold monomial
  rw [Finset.prod_eq_single x]
  · simp
  · intro y _ hy; rw [Pi.single_eq_of_ne hy]; simp
  · intro h; simp at h


lemma isSpinMonomial_bond (e : Sym2 V) : IsSpinMonomial (fun s => bond s e) := by
  induction e with
  | h a b =>
    have : (fun s : ConfigSpace V => bond s s(a, b))
        = (fun s => (fun s => spin s a) s * (fun s => spin s b) s) := by
      funext s; rw [bond_mk]
    rw [this]
    exact (isSpinMonomial_spin a).mul (isSpinMonomial_spin b)


lemma gks_kernel {ι : Type*} (I : Finset ι) (c d : ι → ℝ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hd : ∀ i ∈ I, 0 ≤ d i)
    (fac : ι → ConfigSpace V → ℝ) (hfac : ∀ i ∈ I, IsSpinMonomial (fac i))
    (obs : ConfigSpace V → ℝ) (hobs : IsSpinMonomial obs) :
    0 ≤ ∑ s : ConfigSpace V, obs s * ∏ i ∈ I, (c i + d i * fac i s) := by
  classical
  induction I using Finset.induction generalizing obs with
  | empty =>
    simp only [Finset.prod_empty, mul_one]
    exact hobs.sum_nonneg
  | @insert a I ha IH =>
    have hca : 0 ≤ c a := hc a (Finset.mem_insert_self a I)
    have hda : 0 ≤ d a := hd a (Finset.mem_insert_self a I)
    have hc' : ∀ i ∈ I, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ I, 0 ≤ d i := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hfac' : ∀ i ∈ I, IsSpinMonomial (fac i) :=
      fun i hi => hfac i (Finset.mem_insert_of_mem hi)
    have hfaca : IsSpinMonomial (fac a) := hfac a (Finset.mem_insert_self a I)
    have expand : ∀ s : ConfigSpace V,
        obs s * ∏ i ∈ insert a I, (c i + d i * fac i s)
        = c a * (obs s * ∏ i ∈ I, (c i + d i * fac i s))
          + d a * ((fun s => obs s * fac a s) s * ∏ i ∈ I, (c i + d i * fac i s)) := by
      intro s; rw [Finset.prod_insert ha]; simp only; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_nonneg (mul_nonneg hca (IH hc' hd' hfac' obs hobs))
      (mul_nonneg hda (IH hc' hd' hfac' _ (hobs.mul hfaca)))


end Ising
end StatMech
