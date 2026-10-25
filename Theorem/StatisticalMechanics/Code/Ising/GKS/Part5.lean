/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.GKS.Part5
open scoped BigOperators
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] in

lemma bond_eq_pm (s : ConfigSpace V) (e : Sym2 V) : bond s e = 1 ∨ bond s e = -1 := by
  induction e with
  | h x y =>
    rw [bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]

omit [Fintype V] [DecidableEq V] in

lemma spin_eq_pm (s : ConfigSpace V) (x : V) : spin s x = 1 ∨ spin s x = -1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]

omit [DecidableEq V] in

lemma exp_mul_pm (c t : ℝ) (ht : t = 1 ∨ t = -1) :
    Real.exp (c * t) = Real.cosh c + t * Real.sinh c := by
  rw [Real.cosh_eq, Real.sinh_eq]
  rcases ht with h | h <;> subst h
  · ring_nf
  · rw [mul_neg_one]; ring

omit [DecidableEq V] in


lemma isingWeight_factor (β h : ℝ) (s : ConfigSpace V) :
    isingWeight G β h s
      = (∏ e ∈ G.edgeFinset, (Real.cosh β + bond s e * Real.sinh β))
        * (∏ x : V, (Real.cosh (β * h) + spin s x * Real.sinh (β * h))) := by
  unfold isingWeight hamiltonian
  have hexp : -β * (-(∑ e ∈ G.edgeFinset, bond s e) - h * ∑ x, spin s x)
      = (∑ e ∈ G.edgeFinset, β * bond s e) + (∑ x, (β * h) * spin s x) := by
    have e1 : (∑ e ∈ G.edgeFinset, β * bond s e) = β * ∑ e ∈ G.edgeFinset, bond s e := by
      rw [Finset.mul_sum]
    have e2 : (∑ x, (β * h) * spin s x) = (β * h) * ∑ x, spin s x := by rw [Finset.mul_sum]
    rw [e1, e2]; ring
  rw [hexp, Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · exact Finset.prod_congr rfl (fun e _ => exp_mul_pm β (bond s e) (bond_eq_pm s e))
  · exact Finset.prod_congr rfl (fun x _ => exp_mul_pm (β * h) (spin s x) (spin_eq_pm s x))


lemma sum_spinProd_isingWeight_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (A : Finset V) :
    0 ≤ ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
  classical
  
  set ce : Sym2 V ⊕ V → ℝ := Sum.elim (fun _ => Real.cosh β) (fun _ => Real.cosh (β * h))
  set de : Sym2 V ⊕ V → ℝ := Sum.elim (fun _ => Real.sinh β) (fun _ => Real.sinh (β * h))
  set fac : (Sym2 V ⊕ V) → ConfigSpace V → ℝ :=
    Sum.elim (fun e s => bond s e) (fun x s => spin s x)
  
  set I : Finset (Sym2 V ⊕ V) :=
    G.edgeFinset.map ⟨Sum.inl, Sum.inl_injective⟩
      ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  
  have hint : ∀ s : ConfigSpace V,
      spinProd A s * isingWeight G β h s
        = spinProd A s * ∏ i ∈ I, (ce i + de i * fac i s) := by
    intro s
    rw [isingWeight_factor]
    congr 1
    have hdisj : Disjoint (G.edgeFinset.map ⟨Sum.inl, Sum.inl_injective⟩)
        ((Finset.univ : Finset V).map ⟨Sum.inr, Sum.inr_injective⟩) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi hj
      obtain ⟨a, _, rfl⟩ := hi
      obtain ⟨b, _, hb⟩ := hj
      exact Sum.inl_ne_inr hb.symm
    rw [Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
    simp only [ce, de, fac, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.prod_congr rfl (fun e _ => by ring)
    · exact Finset.prod_congr rfl (fun x _ => by ring)
  simp_rw [hint]
  
  apply gks_kernel I ce de
  · 
    intro i _; rcases i with e | x
    · exact (Real.cosh_pos β).le
    · exact (Real.cosh_pos (β * h)).le
  · 
    intro i _; rcases i with e | x
    · exact Real.sinh_nonneg_iff.mpr hβ
    · exact Real.sinh_nonneg_iff.mpr (mul_nonneg hβ hh)
  · 
    intro i _; rcases i with e | x
    · exact isSpinMonomial_bond e
    · exact isSpinMonomial_spin x
  · 
    exact isSpinMonomial_spinProd A


theorem gks_first (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    0 ≤ isingExpectation G β h (spinProd A) := by
  unfold isingExpectation isingProb
  
  have hrw : ∀ s : ConfigSpace V,
      isingWeight G β h s / isingZ G β h * spinProd A s
        = (isingZ G β h)⁻¹ * (spinProd A s * isingWeight G β h s) := by
    intro s; rw [div_eq_mul_inv]; ring
  simp_rw [hrw]
  rw [← Finset.mul_sum]
  exact mul_nonneg (inv_nonneg.mpr (isingZ_pos G β h).le)
    (sum_spinProd_isingWeight_nonneg G β h hβ hh A)

end Ising
end StatMech
