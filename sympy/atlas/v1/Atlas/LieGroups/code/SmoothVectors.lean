/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SmoothVectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.ContinuousRep
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

open scoped Manifold

namespace ContinuousRep

section SmoothVectors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def orbitMap (π : ContinuousRep G F) (v : F) : G → F :=
  fun g => (π.toMonoidHom g) v

def IsSmoothVector (π : ContinuousRep G F) (v : F) : Prop :=
  ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v)

def smoothSubspace (π : ContinuousRep G F) : Submodule ℂ F where
  carrier := { v | π.IsSmoothVector I v }
  zero_mem' := by
    show π.IsSmoothVector I 0
    unfold IsSmoothVector orbitMap
    have : (fun g : G => (π.toMonoidHom g) (0 : F)) = fun _ => 0 := by
      ext g; exact map_zero _
    rw [this]; exact contMDiff_const
  add_mem' := by
    intro v w (hv : π.IsSmoothVector I v) (hw : π.IsSmoothVector I w)
    show π.IsSmoothVector I (v + w)
    unfold IsSmoothVector orbitMap at *
    have : (fun g : G => (π.toMonoidHom g) (v + w)) =
           fun g => (π.toMonoidHom g) v + (π.toMonoidHom g) w := by
      ext g; exact map_add _ _ _
    rw [this]; exact hv.add hw
  smul_mem' := by
    intro c v (hv : π.IsSmoothVector I v)
    show π.IsSmoothVector I (c • v)
    unfold IsSmoothVector orbitMap at *
    let L : F →L[ℝ] F := {
      toFun := fun w => c • w
      map_add' := smul_add c
      map_smul' := fun r w => (smul_comm r c w).symm
      cont := continuous_const_smul c
    }
    have heq : (fun g : G => (π.toMonoidHom g) (c • v)) =
               L ∘ (fun g => (π.toMonoidHom g) v) := by
      ext g; exact ContinuousLinearMap.map_smul _ _ _
    rw [heq]; exact L.contMDiff.comp hv

def derivedRep (π : ContinuousRep G F) (lieExp : E → G) (X : E)
    (v : F) : F :=
  deriv (fun t : ℝ => (π.toMonoidHom (lieExp (t • X))) v) 0

end SmoothVectors

end ContinuousRep

end
