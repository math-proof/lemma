/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Axiomatic interface for the **cotangent bundle** $T^*X$ of a manifold $X$: equips $T^*X$ with
the tautological Liouville 1-form $\theta$, the canonical symplectic form $\omega = d\theta$, and a
zero section $X \hookrightarrow T^*X$ along which $\theta$ pulls back to $0$. -/
class CotangentBundleDFS
    (Ω_X : ℕ → Type*) (VF_X : Type*)
    (Ω_TX : ℕ → Type*) (VF_TX : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_TX : DifferentialFormSpace Ω_TX VF_TX] where
  dimX : ℕ
  dimX_pos : 0 < dimX
  liouville : Ω_TX 1
  canonical_symplectic : SymplecticManifold Ω_TX VF_TX
  symplectic_eq_d_liouville : canonical_symplectic.ω = inst_TX.d liouville
  zeroSection : DFSMorphism Ω_X VF_X Ω_TX VF_TX
  liouville_zero_section : zeroSection.pullback liouville = (0 : Ω_X 1)


