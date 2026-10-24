/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Algebra.Module.Basic

open ContinuousAlternatingMap

/-- A (concrete) differential $n$-form on a normed space $E$: a smooth map assigning to each point an alternating continuous $n$-linear form. -/
abbrev DiffForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
  E → E [⋀^Fin n]→L[ℝ] ℝ

/-- Pullback of a differential form along a smooth map: $(f^*\omega)_x(v_1,\dots,v_n) = \omega_{f(x)}(df_x v_1, \dots, df_x v_n)$. -/
noncomputable def pullbackForm {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (f : E₁ → E₂) {n : ℕ} (ω : DiffForm E₂ n) : DiffForm E₁ n :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

namespace DeRhamConcrete

section CohomologyIsomorphism

variable {E_X E_U : Type*}
  [NormedAddCommGroup E_X] [NormedSpace ℝ E_X]
  [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]

/-- Concrete deformation retract data $i : X \hookrightarrow U$ and $\pi : U \to X$ with a chain homotopy operator $K$ satisfying $dK + Kd = \mathrm{id} - \pi^* i^*$, used to prove $i^* : H^*(U) \xrightarrow{\sim} H^*(X)$. -/
structure HasDeformationRetractConcrete
    (i : E_X → E_U) (π : E_U → E_X) where
  smooth_i : ContDiff ℝ ⊤ i
  smooth_π : ContDiff ℝ ⊤ π
  retraction : ∀ {n : ℕ} (ω : DiffForm E_X n),
    pullbackForm i (pullbackForm π ω) = ω
  K : ∀ {p : ℕ}, DiffForm E_U (p + 1) → DiffForm E_U p
  K_smul : ∀ {p : ℕ} (r : ℝ) (β : DiffForm E_U (p + 1)),
    K (r • β) = r • K β
  homotopy_formula : ∀ {p : ℕ} (β : DiffForm E_U (p + 1)),
    extDeriv (K β) + K (extDeriv β) = β - pullbackForm π (pullbackForm i β)
  K_vanishes : ∀ {p : ℕ} (β : DiffForm E_U (p + 1)),
    pullbackForm i (K β) = 0
  deg0_injectivity : ∀ (β : DiffForm E_U 0),
    extDeriv β = 0 → pullbackForm i β = 0 → β = 0
  smooth_forms_U : ∀ {n : ℕ} (ω : DiffForm E_U n), ContDiff ℝ ⊤ ω

namespace HasDeformationRetractConcrete

variable {i : E_X → E_U} {π : E_U → E_X}

/-- Pullback along the identity is the identity: $\mathrm{id}^*\omega = \omega$. -/
lemma pullbackForm_id {n : ℕ} (ω : DiffForm E n) :
    pullbackForm id ω = ω := by
  ext x v
  simp [pullbackForm, fderiv_id, ContinuousAlternatingMap.compContinuousLinearMap]

/-- The exterior derivative of the zero form is zero: $d 0 = 0$. -/
lemma extDeriv_zero_eq_zero {n : ℕ} :
    extDeriv (0 : DiffForm E n) = (0 : DiffForm E (n + 1)) := by
  funext x
  change ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (0 : E → E [⋀^Fin n]→L[ℝ] ℝ) x) = 0
  rw [show (0 : E → E [⋀^Fin n]→L[ℝ] ℝ) = Function.const E 0 from rfl]
  simp [ContinuousAlternatingMap.alternatizeUncurryFin, ContinuousLinearMap.map_zero]

/-- Any function out of a subsingleton normed space is smooth (it is constant). -/
lemma contDiff_of_subsingleton_domain {E' F : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Subsingleton E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E' → F) : ContDiff ℝ ⊤ f := by
  have : f = Function.const E' (f 0) := by
    ext x; have h : x = 0 := Subsingleton.elim x 0; subst h; rfl
  rw [this]; exact contDiff_const

/-- The trivial deformation retract instance on a subsingleton (e.g., a point), with $K \equiv 0$. -/
noncomputable def DeRhamConcrete.HasDeformationRetractConcrete.ofSubsingleton
    (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Subsingleton E'] :
    HasDeformationRetractConcrete (id : E' → E') (id : E' → E') where
  smooth_i := contDiff_id
  smooth_π := contDiff_id
  retraction := fun ω => by rw [pullbackForm_id, pullbackForm_id]
  K := fun _ => 0
  K_smul := fun r β => by simp
  homotopy_formula := fun {p} β => by
    simp only [pullbackForm_id, sub_self]
    rw [extDeriv_zero_eq_zero]
    simp
  K_vanishes := fun _ => by
    ext x v; simp [pullbackForm]
  deg0_injectivity := fun β _ h => by
    rw [pullbackForm_id] at h; exact h
  smooth_forms_U := fun ω => contDiff_of_subsingleton_domain ω

end Instances
