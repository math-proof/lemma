import Mathlib
import Def.ExtEndgame_ProductionDatum
import Lemma.Rep.ContinuousH1
import Def.GroupCohomology_PoitouTate

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory ExtCitation

noncomputable section

namespace IntermediateField

def IsUnramifiedOutside (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (S : Finset Nat.Primes) : Prop :=
  FiniteDimensional ℚ F ∧ ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
    A.LiesOverPrime (q : ℕ) → A.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup

end IntermediateField

namespace groupCohomology

variable (S : Finset Nat.Primes)

def IsLevelConstantS₁ {X : Type*} (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g s, s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstantS₂ {X : Type*}
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g g' s s', s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g')

variable {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def levelCochainsS₁ : Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) where
  carrier := {f | IsLevelConstantS₁ S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantS₁_const S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCochainsS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) where
  carrier := {f | IsLevelConstantS₂ S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantS₂_const S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCocyclesS₁ : Submodule k (cocycles₁ M) :=
  (levelCochainsS₁ S M).comap (cocycles₁ M).subtype

def continuousH1S : Submodule k (H1 M) :=
  (levelCocyclesS₁ S M).map (H1π M).hom

variable {S} in

def levelCocyclesS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :=
  cocycles₂ M ⊓ levelCochainsS₂ S M

def levelCoboundariesS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :=
  (levelCochainsS₁ S M).map (d₁₂ M).hom

abbrev continuousH2S : Type :=
  ↥(levelCocyclesS₂ S M) ⧸ (levelCoboundariesS₂ S M).comap (levelCocyclesS₂ S M).subtype

abbrev continuousH2Sπ : ↥(levelCocyclesS₂ S M) →ₗ[k] continuousH2S S M :=
  Submodule.mkQ _

def levelCocyclesS₂ToLevelCocycles₂ : ↥(levelCocyclesS₂ S M) →ₗ[k] ↥(levelCocycles₂ (MonoidHom.id _) M) :=
  Submodule.inclusion (levelCocyclesS₂_le_levelCocycles₂ S M)

noncomputable def continuousH2SToContinuousH2 : continuousH2S S M →ₗ[k] continuousH2 (MonoidHom.id _) M :=
  Submodule.mapQ _ _ (levelCocyclesS₂ToLevelCocycles₂ S M) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    exact levelCoboundariesS₂_le_levelCoboundaries₂ S M hc)

noncomputable def locRes₂S {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    continuousH2S S M →ₗ[k] continuousH2 f (Rep.res f M) :=
  continuousH2Map (rH := MonoidHom.id _) (rG := f) f (fun _ => rfl)
      (LinearMap.id : M →ₗ[k] Rep.res f M) (fun _ _ => rfl)
    ∘ₗ continuousH2SToContinuousH2 S M

noncomputable def locTotal₂S :
    continuousH2S S M →ₗ[k] ∀ v : extArithIndex S, continuousH2 (extArithLoc S v) (Rep.res (extArithLoc S v) M) :=
  LinearMap.pi fun v => locRes₂S S M (extArithLoc S v)

noncomputable def sha₂ : Submodule k (continuousH2S S M) :=
  LinearMap.ker (locTotal₂S S M)

section Sha
variable {K : Type} [Field K] (A : Rep K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def sha₁ : Submodule K (H1 A) :=
  continuousH1S S A ⊓ LinearMap.ker (locTotal (extArithLoc S) A)

end Sha

end groupCohomology

end
