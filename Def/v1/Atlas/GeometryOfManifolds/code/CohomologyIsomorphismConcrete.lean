/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CohomologyIsomorphismConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Abbrev.v1.Atlas.GeometryOfManifolds.code.CohomologyIsomorphismConcrete

@[expose] public section

open ContinuousAlternatingMap


/-- Pullback of a differential form along a smooth map: $(f^*\omega)_x(v_1,\dots,v_n) = \omega_{f(x)}(df_x v_1, \dots, df_x v_n)$. -/
noncomputable def pullbackForm {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (f : E₁ → E₂) {n : ℕ} (ω : DiffForm E₂ n) : DiffForm E₁ n :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

