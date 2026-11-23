module

public import Mathlib
public import Theorem.Submodule.ContinuousH2
public import Theorem.Rep.ContinuousH1

public noncomputable section

set_option autoImplicit false
open CategoryTheory


noncomputable section

namespace IntermediateField


public theorem isUnramifiedOutside_bot (S : Finset Nat.Primes) :
    (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by
  refine ⟨inferInstance, fun q _ A _ σ _ => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes r


public theorem IsUnramifiedOutside.sup {S : Finset Nat.Primes} {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S) : (F ⊔ F').IsUnramifiedOutside S := by
  have := hF.1
  have := hF'.1
  refine ⟨IntermediateField.finiteDimensional_sup F F', fun q hq A hA σ hσ => ?_⟩
  rw [IntermediateField.fixingSubgroup_sup]
  exact ⟨hF.2 q hq A hA hσ, hF'.2 q hq A hA hσ⟩


public theorem IsUnramifiedOutside.mono {S S' : Finset Nat.Primes} (h : S ⊆ S') {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) : F.IsUnramifiedOutside S' :=
  ⟨hF.1, fun q hq A hA => hF.2 q (fun hqS => hq (h hqS)) A hA⟩


public theorem IsUnramifiedOutside.of_le {S : Finset Nat.Primes} {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : F' ≤ F)
    (hF : F.IsUnramifiedOutside S) : F'.IsUnramifiedOutside S := by
  have := hF.1
  exact ⟨FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle),
    fun q hq A hA => (hF.2 q hq A hA).trans (IntermediateField.fixingSubgroup_antitone hle)⟩

end IntermediateField

namespace groupCohomology

universe u

variable {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)


public theorem isLevelConstantSr₁_id_iff {X : Type*} (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) :
    IsLevelConstantSr₁ (MonoidHom.id _) S f ↔ IsLevelConstantS₁ S f := Iff.rfl


public theorem isLevelConstantSr₂_id_iff {X : Type*}
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) :
    IsLevelConstantSr₂ (MonoidHom.id _) S f ↔ IsLevelConstantS₂ S f := Iff.rfl

variable {r S}


public theorem IsLevelConstantSr₁.isLevelConstant₁ {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) : IsLevelConstant₁ r f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, h⟩


public theorem IsLevelConstantSr₂.isLevelConstant₂ {X : Type*} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) : IsLevelConstant₂ r f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, h⟩


public theorem IsLevelConstantSr₁.add {X : Type*} [Add X] {f f' : G → X} (hf : IsLevelConstantSr₁ r S f) (hf' : IsLevelConstantSr₁ r S f') :
    IsLevelConstantSr₁ r S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]


public theorem IsLevelConstantSr₂.add {X : Type*} [Add X] {f f' : G × G → X} (hf : IsLevelConstantSr₂ r S f)
    (hf' : IsLevelConstantSr₂ r S f') : IsLevelConstantSr₂ r S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.add_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

variable (r S) in

public theorem isLevelConstantSr₁_const {X : Type*} (x : X) : IsLevelConstantSr₁ r S (fun _ : G => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩

variable (r S) in

public theorem isLevelConstantSr₂_const {X : Type*} (x : X) : IsLevelConstantSr₂ r S (fun _ : G × G => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ _ _ _ => rfl⟩


public theorem IsLevelConstantSr₁.comp {X Y : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) (φ : X → Y) :
    IsLevelConstantSr₁ r S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩


public theorem IsLevelConstantSr₂.comp {X Y : Type*} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) (φ : X → Y) :
    IsLevelConstantSr₂ r S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩


public theorem IsLevelConstantSr₁.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) :
    IsLevelConstantSr₁ r S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩


public theorem IsLevelConstantSr₂.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*} {f : G × G → X}
    (hf : IsLevelConstantSr₂ r S f) : IsLevelConstantSr₂ r S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩


public theorem IsLevelConstantSr₁.of_comp {G' : Type*} [Group G'] (ι : G' →* G) {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) :
    IsLevelConstantSr₁ (r.comp ι) S (f ∘ ι) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, map_mul, h (ι g) (ι s) hs]⟩


public theorem IsLevelConstantSr₂.of_comp {G' : Type*} [Group G'] (ι : G' →* G) {X : Type*} {f : G × G → X}
    (hf : IsLevelConstantSr₂ r S f) : IsLevelConstantSr₂ (r.comp ι) S (f ∘ Prod.map ι ι) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, Prod.map_apply, map_mul, h _ _ _ _ hs hs']⟩

section carriers

variable (r S) {k : Type u} [CommRing k] (M : Rep k G)


public theorem mem_levelCochainsSr₁_iff (f : G → M) : f ∈ levelCochainsSr₁ r S M ↔ IsLevelConstantSr₁ r S f := Iff.rfl


public theorem mem_levelCochainsSr₂_iff (f : G × G → M) : f ∈ levelCochainsSr₂ r S M ↔ IsLevelConstantSr₂ r S f := Iff.rfl


public theorem levelCochainsSr₁_le_levelCochains₁ : levelCochainsSr₁ r S M ≤ levelCochains₁ r M :=
  fun _ hf => hf.isLevelConstant₁


public theorem levelCochainsSr₂_le_levelCochains₂ : levelCochainsSr₂ r S M ≤ levelCochains₂ r M :=
  fun _ hf => hf.isLevelConstant₂


public theorem mem_levelCocyclesSr₁_iff (c : cocycles₁ M) : c ∈ levelCocyclesSr₁ r S M ↔ IsLevelConstantSr₁ r S c := Iff.rfl


public theorem mem_continuousH1Sr_iff (x : H1 M) :
    x ∈ continuousH1Sr r S M ↔ ∃ c : cocycles₁ M, IsLevelConstantSr₁ r S c ∧ (H1π M).hom c = x := by
  simp only [continuousH1Sr, Submodule.mem_map, mem_levelCocyclesSr₁_iff]


public theorem H1π_mem_continuousH1Sr {c : cocycles₁ M} (hc : IsLevelConstantSr₁ r S c) : (H1π M).hom c ∈ continuousH1Sr r S M :=
  (mem_continuousH1Sr_iff r S M _).2 ⟨c, hc, rfl⟩


public theorem continuousH1Sr_le_continuousH1 : continuousH1Sr r S M ≤ continuousH1 r M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff r S M x).1 hx
  exact H1π_mem_continuousH1 r M hc.isLevelConstant₁

variable {S} in


public theorem continuousH1Sr_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH1Sr r S M ≤ continuousH1Sr r S' M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff r S M x).1 hx
  exact (mem_continuousH1Sr_iff r S' M _).2 ⟨c, hc.mono h, rfl⟩


public theorem mem_levelCocyclesSr₂_iff (f : G × G → M) : f ∈ levelCocyclesSr₂ r S M ↔ f ∈ cocycles₂ M ∧ IsLevelConstantSr₂ r S f :=
  Iff.rfl


public theorem mem_levelCoboundariesSr₂_iff (f : G × G → M) :
    f ∈ levelCoboundariesSr₂ r S M ↔ ∃ x : G → M, IsLevelConstantSr₁ r S x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundariesSr₂, Submodule.mem_map, mem_levelCochainsSr₁_iff]


public theorem levelCocyclesSr₂_le_levelCocycles₂ : levelCocyclesSr₂ r S M ≤ levelCocycles₂ r M :=
  fun _ h => ⟨h.1, h.2.isLevelConstant₂⟩


public theorem levelCocyclesSr₂_le_cocycles₂ : levelCocyclesSr₂ r S M ≤ cocycles₂ M := fun _ h => h.1


public theorem levelCoboundariesSr₂_le_levelCoboundaries₂ : levelCoboundariesSr₂ r S M ≤ levelCoboundaries₂ r M := by
  rintro f hf
  obtain ⟨x, hx, rfl⟩ := (mem_levelCoboundariesSr₂_iff r S M f).1 hf
  exact (mem_levelCoboundaries₂_iff r M _).2 ⟨x, hx.isLevelConstant₁, rfl⟩


public theorem levelCoboundariesSr₂_le_coboundaries₂ : levelCoboundariesSr₂ r S M ≤ coboundaries₂ M :=
  (levelCoboundariesSr₂_le_levelCoboundaries₂ r S M).trans (levelCoboundaries₂_le_coboundaries₂ r M)

variable {S} in

public theorem levelCocyclesSr₂_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : levelCocyclesSr₂ r S M ≤ levelCocyclesSr₂ r S' M :=
  fun _ hf => ⟨hf.1, hf.2.mono h⟩


public theorem continuousH2Srπ_eq_zero_iff (f : ↥(levelCocyclesSr₂ r S M)) :
    continuousH2Srπ r S M f = 0 ↔ (f : G × G → M) ∈ levelCoboundariesSr₂ r S M := by
  simp [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]


public theorem continuousH2Srπ_surjective : Function.Surjective (continuousH2Srπ r S M) :=
  Submodule.mkQ_surjective _


public theorem continuousH2SrToContinuousH2_mk (c : ↥(levelCocyclesSr₂ r S M)) :
    continuousH2SrToContinuousH2 r S M (continuousH2Srπ r S M c) = continuousH2π r M (levelCocyclesSr₂ToLevelCocycles₂ r S M c) := rfl

variable {S} in

