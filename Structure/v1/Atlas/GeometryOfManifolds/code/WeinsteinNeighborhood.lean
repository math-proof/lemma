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
import Def.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part3
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- A *relative homotopy operator* for an inclusion $i : X \hookrightarrow U$ packages
the chain-level data showing that $i^*$ is a homotopy equivalence:
a retraction $\pi : U \to X$, a chain homotopy
$K : \Omega^{p+1}(U) \to \Omega^p(U)$ satisfying
$dK + Kd = \mathrm{id} - \pi^* i^*$, and the additional condition $i^* K = 0$
(so that primitives vanish on $X$). -/
structure HasRelativeHomotopyOperator
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    (Ω_X : ℕ → Type*) (VF_X : Type*) [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF) where
  π : DFSMorphism Ω VF Ω_X VF_X
  retraction : ∀ {p : ℕ} (α : Ω_X p), i.pullback (π.pullback α) = α
  K : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  K_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), K (r • α) = r • K α
  homotopy_formula : ∀ {p : ℕ} (β : Ω (p + 1)),
    inst.d (K β) + K (inst.d β) = β - π.pullback (i.pullback β)
  K_vanishes_on_X : ∀ {p : ℕ} (β : Ω (p + 1)), i.pullback (K β) = 0


