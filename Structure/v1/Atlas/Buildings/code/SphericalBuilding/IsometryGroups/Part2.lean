/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part2
set_option linter.unusedSectionVars false


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- A **(B,N)-pair** in the isometry group of $(V,B)$: data of a Borel-type subgroup
stabilising a maximal isotropic flag, a frame-stabiliser playing the role of $N$, and a torus
$T = B \cap N$, satisfying the standard compatibility properties. -/
structure IsometryBNPair (B : LinearMap.BilinForm k V) (n : ℕ) where
  borel : Subgroup (V ≃ₗ[k] V)
  maxFlag : IsotropicFlag B
  borel_isometry : ∀ g ∈ borel, ∀ v₁ v₂ : V,
    B ((g : V ≃ₗ[k] V) v₁) ((g : V ≃ₗ[k] V) v₂) = B v₁ v₂
  borel_stabilizes : ∀ g ∈ borel, ∀ i,
    (maxFlag.chain i).map (g : V ≃ₗ[k] V).toLinearMap = maxFlag.chain i
  frameStab : Subgroup (V ≃ₗ[k] V)
  frame : HyperbolicFrame B n
  frameStab_isometry : ∀ g ∈ frameStab, ∀ v₁ v₂ : V,
    B ((g : V ≃ₗ[k] V) v₁) ((g : V ≃ₗ[k] V) v₂) = B v₁ v₂
  frameStab_permutes : ∀ g ∈ frameStab,
    ∀ i : Fin n, ∃ j : Fin n,
      (g : V ≃ₗ[k] V) (frame.pairs i).e = (frame.pairs j).e ∨
      (g : V ≃ₗ[k] V) (frame.pairs i).e = (frame.pairs j).e'
  frameStab_permutes_e' : ∀ g ∈ frameStab,
    ∀ i : Fin n, ∃ j : Fin n,
      (g : V ≃ₗ[k] V) (frame.pairs i).e' = (frame.pairs j).e ∨
      (g : V ≃ₗ[k] V) (frame.pairs i).e' = (frame.pairs j).e'
  torus : Subgroup (V ≃ₗ[k] V)
  torus_eq : (torus : Set (V ≃ₗ[k] V)) = (borel : Set (V ≃ₗ[k] V)) ∩ (frameStab : Set (V ≃ₗ[k] V))


end IsometryBuilding
