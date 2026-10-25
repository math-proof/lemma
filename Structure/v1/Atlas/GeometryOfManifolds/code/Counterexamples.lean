/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
set_option autoImplicit false

open DifferentialFormSpace


/-- Data witnessing the Hopf surface: a compact complex manifold with $H^2$ trivial and which admits no symplectic structure. -/
structure HopfSurfaceData where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  J : @AlmostComplexStr Ω VF inst
  nij : @NijenhuisTensor Ω VF inst J
  integrable : @IsIntegrable Ω VF inst J nij
  h2_trivial : ∀ (ω : Ω 2), inst.d ω = 0 → ∃ (β : Ω 1), inst.d β = ω
  not_symplectic : ¬ Nonempty (@SymplecticManifold Ω VF inst)


/-- Data witnessing the $4$-sphere $S^4$: a compact manifold which admits no symplectic structure (every closed $2$-form is exact, so $\omega^2$ cannot be a volume form). -/
structure S4Data where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  compact : @IsCompactSymplectic Ω VF inst
  h2_trivial : ∀ (α : Ω 2), inst.d α = 0 → ∃ (β : Ω 1), α = inst.d β


/-- The fundamental group $\Gamma$ of the Kodaira–Thurston manifold, presented as quadruples $(a,b,c,d) \in \mathbb{Z}^4$ with a twisted multiplication. -/
structure KTGamma where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

