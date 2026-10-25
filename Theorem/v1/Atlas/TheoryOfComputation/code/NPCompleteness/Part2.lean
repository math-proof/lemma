/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part4


namespace CookLevin

open TuringMachine NPCompleteness

/--
Soundness of the Tseitin auxiliary construction: if `σ` satisfies all the
clauses produced by `tseitinAux φ fresh`, then `σ` of the root variable equals
the value of `φ` under `σ`.
-/
lemma tseitinAux_soundness : ∀ (φ : BoolFormula) (fresh : ℕ) (σ : BoolAssignment),
    (∀ c ∈ (tseitinAux φ fresh).2.1, c.eval σ = true) →
    σ (tseitinAux φ fresh).1 = φ.eval σ
  | .var n, _, σ, _ => rfl
  | .trueConst, fresh, σ, hcls => by
    simp only [tseitinAux, BoolFormula.eval] at hcls ⊢
    have h := hcls (mk3Clause (.var fresh) (.var fresh) (.var fresh)) (by simp)
    simp [mk3Clause, BoolFormula.eval] at h; exact h
  | .falseConst, fresh, σ, hcls => by
    simp only [tseitinAux, BoolFormula.eval] at hcls ⊢
    have h := hcls (mk3Clause (.not (.var fresh)) (.not (.var fresh)) (.not (.var fresh))) (by simp)
    simp [mk3Clause, BoolFormula.eval] at h; exact h
  | .not ψ, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr : tseitinAux ψ fresh = r at hcls ⊢
    obtain ⟨vφ, clsφ, fresh1⟩ := r; simp only at hcls ⊢
    have hih : σ vφ = ψ.eval σ := by
      have := tseitinAux_soundness ψ fresh σ; rw [hr] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ hc))
    have h1 := hcls (mk3Clause (.var vφ) (.var fresh1) (.var fresh1))
      (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]; right; left; trivial)
    have h2 := hcls (mk3Clause (.not (.var vφ)) (.not (.var fresh1)) (.not (.var fresh1)))
      (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]; right; right; trivial)

    simp [mk3Clause, BoolFormula.eval, hih] at h1 h2
    simp only [BoolFormula.eval]; cases he : ψ.eval σ <;> simp_all

  | .and ψ₁ ψ₂, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at hcls ⊢
    obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at hcls ⊢
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at hcls ⊢
    obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at hcls ⊢
    have hih1 : σ v₁ = ψ₁.eval σ := by
      have := tseitinAux_soundness ψ₁ fresh σ; rw [hr₁] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hih2 : σ v₂ = ψ₂.eval σ := by
      have := tseitinAux_soundness ψ₂ f1 σ; rw [hr₂] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_right _ hc)))
    have hc1 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; left; trivial)
    have hc2 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; left; trivial)
    have hc3 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; left; trivial)
    have hc4 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; right; left; trivial)
    simp [mk3Clause, BoolFormula.eval, hih1, hih2] at hc1 hc2 hc3 hc4
    simp only [BoolFormula.eval]; cases h1e : ψ₁.eval σ <;> cases h2e : ψ₂.eval σ <;> simp_all
  | .or ψ₁ ψ₂, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at hcls ⊢
    obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at hcls ⊢
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at hcls ⊢
    obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at hcls ⊢
    have hih1 : σ v₁ = ψ₁.eval σ := by
      have := tseitinAux_soundness ψ₁ fresh σ; rw [hr₁] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hih2 : σ v₂ = ψ₂.eval σ := by
      have := tseitinAux_soundness ψ₂ f1 σ; rw [hr₂] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_right _ hc)))
    have hc1 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; left; trivial)
    have hc2 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; left; trivial)
    have hc3 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; left; trivial)
    have hc4 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; right; left; trivial)

    simp [mk3Clause, BoolFormula.eval, hih1, hih2] at hc1 hc2 hc3 hc4
    simp only [BoolFormula.eval]; cases h1e : ψ₁.eval σ <;> cases h2e : ψ₂.eval σ <;> simp_all

end CookLevin
