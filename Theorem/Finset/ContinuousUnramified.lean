module

public import Mathlib
public import Def.ExtEndgame_ProductionDatum
public import Theorem.Rep.ContinuousH1
public import Def.GroupCohomology_PoitouTate

public noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory ExtCitation

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
  haveI := hF.1; haveI := hF'.1
  refine ⟨IntermediateField.finiteDimensional_sup F F', fun q hq A hA σ hσ => ?_⟩
  rw [IntermediateField.fixingSubgroup_sup]
  exact ⟨hF.2 q hq A hA hσ, hF'.2 q hq A hA hσ⟩


public theorem IsUnramifiedOutside.mono {S S' : Finset Nat.Primes} (h : S ⊆ S') {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) : F.IsUnramifiedOutside S' :=
  ⟨hF.1, fun q hq A hA => hF.2 q (fun hqS => hq (h hqS)) A hA⟩


public theorem IsUnramifiedOutside.of_le {S : Finset Nat.Primes} {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : F' ≤ F)
    (hF : F.IsUnramifiedOutside S) : F'.IsUnramifiedOutside S := by
  haveI := hF.1
  exact ⟨FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle),
    fun q hq A hA => (hF.2 q hq A hA).trans (IntermediateField.fixingSubgroup_antitone hle)⟩

end IntermediateField

namespace groupCohomology

variable (S : Finset Nat.Primes)


public theorem IsLevelConstantS₁.isLevelConstant₁ {X : Type*} {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) : IsLevelConstant₁ (MonoidHom.id _) f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, fun g s hs => h g s hs⟩

variable {S} in

public theorem IsLevelConstantS₂.isLevelConstant₂ {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) : IsLevelConstant₂ (MonoidHom.id _) f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, fun g g' s s' hs hs' => h g g' s s' hs hs'⟩

variable {S} in

public theorem IsLevelConstantS₁.add {X : Type*} [Add X] {f f' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) (hf' : IsLevelConstantS₁ S f') : IsLevelConstantS₁ S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

variable {S} in

public theorem IsLevelConstantS₂.add {X : Type*} [Add X]
    {f f' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) (hf' : IsLevelConstantS₂ S f') : IsLevelConstantS₂ S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.add_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]


public theorem isLevelConstantS₁_const {X : Type*} (x : X) :
    IsLevelConstantS₁ S (fun _ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩


public theorem isLevelConstantS₂_const {X : Type*} (x : X) :
    IsLevelConstantS₂ S
      (fun _ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ _ _ _ => rfl⟩

variable {S} in

public theorem IsLevelConstantS₁.comp {X Y : Type*} {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) (φ : X → Y) : IsLevelConstantS₁ S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

variable {S} in

public theorem IsLevelConstantS₂.comp {X Y : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) (φ : X → Y) : IsLevelConstantS₂ S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩

variable {S} in

public theorem IsLevelConstantS₁.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X} (hf : IsLevelConstantS₁ S f) : IsLevelConstantS₁ S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

variable {S} in

public theorem IsLevelConstantS₂.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) : IsLevelConstantS₂ S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

variable {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))


public theorem mem_levelCochainsS₁_iff (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCochainsS₁ S M ↔ IsLevelConstantS₁ S f := Iff.rfl


public theorem mem_levelCochainsS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCochainsS₂ S M ↔ IsLevelConstantS₂ S f := Iff.rfl


public theorem mem_continuousH1S_iff (x : H1 M) :
    x ∈ continuousH1S S M ↔ ∃ c : cocycles₁ M, IsLevelConstantS₁ S c ∧ (H1π M).hom c = x := by
  simp only [continuousH1S, Submodule.mem_map, levelCocyclesS₁, Submodule.mem_comap]; rfl


public theorem continuousH1S_le_continuousH1 : continuousH1S S M ≤ continuousH1 (MonoidHom.id _) M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1S_iff S M x).1 hx
  exact H1π_mem_continuousH1 _ M hc.isLevelConstant₁

variable {S} in


public theorem continuousH1S_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH1S S M ≤ continuousH1S S' M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1S_iff S M x).1 hx
  exact (mem_continuousH1S_iff S' M _).2 ⟨c, hc.mono h, rfl⟩


public theorem mem_levelCocyclesS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCocyclesS₂ S M ↔ f ∈ cocycles₂ M ∧ IsLevelConstantS₂ S f := Iff.rfl


public theorem mem_levelCoboundariesS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCoboundariesS₂ S M ↔
      ∃ x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M, IsLevelConstantS₁ S x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundariesS₂, Submodule.mem_map, mem_levelCochainsS₁_iff]


public theorem levelCocyclesS₂_le_levelCocycles₂ : levelCocyclesS₂ S M ≤ levelCocycles₂ (MonoidHom.id _) M :=
  fun _ h => ⟨h.1, h.2.isLevelConstant₂⟩


public theorem levelCoboundariesS₂_le_levelCoboundaries₂ :
    levelCoboundariesS₂ S M ≤ levelCoboundaries₂ (MonoidHom.id _) M := by
  rintro f hf
  obtain ⟨x, hx, rfl⟩ := (mem_levelCoboundariesS₂_iff S M f).1 hf
  exact (mem_levelCoboundaries₂_iff _ M _).2 ⟨x, hx.isLevelConstant₁, rfl⟩


public theorem continuousH2Sπ_eq_zero_iff (f : ↥(levelCocyclesS₂ S M)) :
    continuousH2Sπ S M f = 0 ↔
      (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
        ∈ levelCoboundariesS₂ S M := by
  simp [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]


@[simp]
public theorem locTotal₂S_apply (x : continuousH2S S M) (v : extArithIndex S) :
    locTotal₂S S M x v = locRes₂S S M (extArithLoc S v) x := rfl

