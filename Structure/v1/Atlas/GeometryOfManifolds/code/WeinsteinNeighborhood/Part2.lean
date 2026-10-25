/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Theorem.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part3
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- *Tubular homotopy primitives* for an inclusion $i : X \hookrightarrow U$: the data of a
retraction $\pi$, an Euler-like vector field $V$, and a "radial integration" operator
$\Phi$ satisfying additivity, scalar-multiplicativity, commutation with $d$, an "FTC"
identity $\Phi(\mathcal{L}_V \beta) = \beta - \pi^* i^*\beta$, and the conditions
$i^*(\iota_V \beta) = 0$ and $i^* \Phi = i^*$.

Such primitives canonically produce a relative homotopy operator via
$K := \Phi \circ \iota_V$. -/
structure HasTubularHomotopyPrimitives
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    (Ω_X : ℕ → Type*) (VF_X : Type*) [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF) where
  π : DFSMorphism Ω VF Ω_X VF_X
  retraction : ∀ {p : ℕ} (α : Ω_X p), i.pullback (π.pullback α) = α
  V : VF
  Φ : ∀ {p : ℕ}, Ω p → Ω p
  Φ_add : ∀ {p : ℕ} (γ₁ γ₂ : Ω p), Φ (γ₁ + γ₂) = Φ γ₁ + Φ γ₂
  Φ_smul : ∀ {p : ℕ} (r : ℝ) (γ : Ω p), Φ (r • γ) = r • Φ γ
  Φ_d : ∀ {p : ℕ} (γ : Ω p), inst.d (Φ γ) = Φ (inst.d γ)
  Φ_FTC : ∀ {p : ℕ} (β : Ω (p + 1)), Φ (inst.L V β) = β - π.pullback (i.pullback β)
  ιV_vanish_on_X : ∀ {p : ℕ} (β : Ω (p + 1)), i.pullback (inst.ι V β) = 0
  Φ_fix_X : ∀ {p : ℕ} (γ : Ω p), i.pullback (Φ γ) = i.pullback γ

