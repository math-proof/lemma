import Mathlib
import Def.Submodule_ContinuousH2
import Lemma.Rep.ContinuousH1

set_option autoImplicit false
open CategoryTheory


noncomputable section

namespace IntermediateField

def IsUnramifiedOutside (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (S : Finset Nat.Primes) : Prop :=
  FiniteDimensional ℚ F ∧ ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
    (q : AlgebraicClosure ℚ) ∈ A.nonunits →
    (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype ≤ F.fixingSubgroup

end IntermediateField

namespace groupCohomology

universe u

variable {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

def IsLevelConstantSr₁ {X : Type*} (f : G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstantSr₂ {X : Type*} (f : G × G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g')

def IsLevelConstantS₁ {X : Type*} (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g s, s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstantS₂ {X : Type*}
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g g' s s', s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g')

variable {r S}

section carriers

variable (r S) {k : Type u} [CommRing k] (M : Rep k G)

def levelCochainsSr₁ : Submodule k (G → M) where
  carrier := {f | IsLevelConstantSr₁ r S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantSr₁_const r S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCochainsSr₂ : Submodule k (G × G → M) where
  carrier := {f | IsLevelConstantSr₂ r S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantSr₂_const r S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCocyclesSr₁ : Submodule k (cocycles₁ M) :=
  (levelCochainsSr₁ r S M).comap (cocycles₁ M).subtype

def continuousH1Sr : Submodule k (H1 M) :=
  (levelCocyclesSr₁ r S M).map (H1π M).hom

variable {S} in

def levelCocyclesSr₂ : Submodule k (G × G → M) :=
  cocycles₂ M ⊓ levelCochainsSr₂ r S M

def levelCoboundariesSr₂ : Submodule k (G × G → M) :=
  (levelCochainsSr₁ r S M).map (d₁₂ M).hom

variable {S} in
abbrev continuousH2Sr : Type u :=
  ↥(levelCocyclesSr₂ r S M) ⧸ (levelCoboundariesSr₂ r S M).comap (levelCocyclesSr₂ r S M).subtype

abbrev continuousH2Srπ : ↥(levelCocyclesSr₂ r S M) →ₗ[k] continuousH2Sr r S M :=
  Submodule.mkQ _

def levelCocyclesSr₂ToLevelCocycles₂ : ↥(levelCocyclesSr₂ r S M) →ₗ[k] ↥(levelCocycles₂ r M) :=
  Submodule.inclusion (levelCocyclesSr₂_le_levelCocycles₂ r S M)

def continuousH2SrToContinuousH2 : continuousH2Sr r S M →ₗ[k] continuousH2 r M :=
  Submodule.mapQ _ _ (levelCocyclesSr₂ToLevelCocycles₂ r S M) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    exact levelCoboundariesSr₂_le_levelCoboundaries₂ r S M hc)

variable {S} in

def continuousH2SrOfLE {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH2Sr r S M →ₗ[k] continuousH2Sr r S' M :=
  Submodule.mapQ _ _ (Submodule.inclusion (levelCocyclesSr₂_mono r M h)) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    obtain ⟨x, hx, hxc⟩ := (mem_levelCoboundariesSr₂_iff r S M _).1 hc
    exact (mem_levelCoboundariesSr₂_iff r S' M _).2 ⟨x, hx.mono h, hxc⟩)

end carriers

end groupCohomology

end
