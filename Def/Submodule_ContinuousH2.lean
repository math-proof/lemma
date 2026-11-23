module

public import Mathlib

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]
variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def IsLevelConstant₁ {X : Type*} (f : G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstant₂ {X : Type*} (f : G × G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup →
      f (g * s, g' * s') = f (g, g')

variable (M : Rep k G)

def levelCochains₁ : Submodule k (G → M) where
  carrier := {f | IsLevelConstant₁ r f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstant₁_const r (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCochains₂ : Submodule k (G × G → M) where
  carrier := {f | IsLevelConstant₂ r f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstant₂_const r (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCocycles₂ : Submodule k (G × G → M) :=
  cocycles₂ M ⊓ levelCochains₂ r M

def levelCoboundaries₂ : Submodule k (G × G → M) :=
  (levelCochains₁ r M).map (d₁₂ M).hom

abbrev continuousH2 : Type u :=
  ↥(levelCocycles₂ r M) ⧸ (levelCoboundaries₂ r M).comap (levelCocycles₂ r M).subtype

abbrev continuousH2π : ↥(levelCocycles₂ r M) →ₗ[k] continuousH2 r M :=
  Submodule.mkQ _

def levelCocyclesToCocycles₂ : ↥(levelCocycles₂ r M) →ₗ[k] ↥(cocycles₂ M) where
  toFun c := ⟨(c : G × G → M), c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def continuousH2ToH2 : continuousH2 r M →ₗ[k] H2 M :=
  Submodule.liftQ _ ((H2π M).hom ∘ₗ levelCocyclesToCocycles₂ r M)
    (fun c hc => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact (H2π_eq_zero_iff _).2 (levelCoboundaries₂_le_coboundaries₂ r M hc))

end groupCohomology

end
