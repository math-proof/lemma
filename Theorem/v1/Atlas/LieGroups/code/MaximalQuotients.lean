/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Lie.OfAssociative
public import Def.v1.Atlas.LieGroups.code.MaximalQuotients.Part4

public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

theorem UniversalEnvelopingAlgebra.lift_centralizes
    {A : Type*} [Ring A] [Algebra R A]
    (f : 𝔤 →ₗ⁅R⁆ A) (E : A) (hf : ∀ x, f x * E = E * f x) :
    ∀ u, UniversalEnvelopingAlgebra.lift R f u * E =
      E * UniversalEnvelopingAlgebra.lift R f u := by
  let C := Subalgebra.centralizer R ({E} : Set A)
  have hfC : ∀ x, f x ∈ C := by
    intro x; rw [Subalgebra.mem_centralizer_iff]
    intro g hg; rw [Set.mem_singleton_iff.mp hg]; exact (hf x).symm
  let f' : 𝔤 →ₗ⁅R⁆ C :=
  { toFun := fun x => ⟨f x, hfC x⟩
    map_add' := fun x y => by ext; simp [map_add]
    map_smul' := fun c x => by ext; simp [map_smul]
    map_lie' := fun {x y} => by
      ext; simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket]; rfl }
  let F' := UniversalEnvelopingAlgebra.lift R f'
  have key : C.val.comp F' = UniversalEnvelopingAlgebra.lift R f := by
    apply UniversalEnvelopingAlgebra.hom_ext R; ext x; simp [f', F']
  intro u
  have hu : UniversalEnvelopingAlgebra.lift R f u ∈ C := by rw [← key]; exact (F' u).2
  rw [Subalgebra.mem_centralizer_iff] at hu
  exact (hu E (Set.mem_singleton E)).symm


end
