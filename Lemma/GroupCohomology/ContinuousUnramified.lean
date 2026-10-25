import Mathlib
import Instance.ExtEndgame_ProductionDatum
import Lemma.GroupCohomology.ContinuousH1
import Lemma.GroupCohomology.PoitouTate

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory ExtCitation

noncomputable section

namespace IntermediateField

def IsUnramifiedOutside (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (S : Finset Nat.Primes) : Prop :=
  FiniteDimensional ℚ F ∧ ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
    A.LiesOverPrime (q : ℕ) → A.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup

lemma isUnramifiedOutside_bot (S : Finset Nat.Primes) :
    (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by
  refine ⟨inferInstance, fun q _ A _ σ _ => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes r

lemma IsUnramifiedOutside.sup {S : Finset Nat.Primes} {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S) : (F ⊔ F').IsUnramifiedOutside S := by
  haveI := hF.1; haveI := hF'.1
  refine ⟨IntermediateField.finiteDimensional_sup F F', fun q hq A hA σ hσ => ?_⟩
  rw [IntermediateField.fixingSubgroup_sup]
  exact ⟨hF.2 q hq A hA hσ, hF'.2 q hq A hA hσ⟩

lemma IsUnramifiedOutside.mono {S S' : Finset Nat.Primes} (h : S ⊆ S') {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) : F.IsUnramifiedOutside S' :=
  ⟨hF.1, fun q hq A hA => hF.2 q (fun hqS => hq (h hqS)) A hA⟩

lemma IsUnramifiedOutside.of_le {S : Finset Nat.Primes} {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : F' ≤ F)
    (hF : F.IsUnramifiedOutside S) : F'.IsUnramifiedOutside S := by
  haveI := hF.1
  exact ⟨FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle),
    fun q hq A hA => (hF.2 q hq A hA).trans (IntermediateField.fixingSubgroup_antitone hle)⟩

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

variable {S} in
lemma IsLevelConstantS₁.isLevelConstant₁ {X : Type*} {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) : IsLevelConstant₁ (MonoidHom.id _) f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, fun g s hs => h g s hs⟩

variable {S} in
lemma IsLevelConstantS₂.isLevelConstant₂ {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) : IsLevelConstant₂ (MonoidHom.id _) f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, fun g g' s s' hs hs' => h g g' s s' hs hs'⟩

variable {S} in
lemma IsLevelConstantS₁.add {X : Type*} [Add X] {f f' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) (hf' : IsLevelConstantS₁ S f') : IsLevelConstantS₁ S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

variable {S} in
lemma IsLevelConstantS₂.add {X : Type*} [Add X]
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

lemma isLevelConstantS₁_const {X : Type*} (x : X) :
    IsLevelConstantS₁ S (fun _ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩

lemma isLevelConstantS₂_const {X : Type*} (x : X) :
    IsLevelConstantS₂ S
      (fun _ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ _ _ _ => rfl⟩

variable {S} in
lemma IsLevelConstantS₁.comp {X Y : Type*} {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) (φ : X → Y) : IsLevelConstantS₁ S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

variable {S} in
lemma IsLevelConstantS₂.comp {X Y : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) (φ : X → Y) : IsLevelConstantS₂ S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩

variable {S} in
lemma IsLevelConstantS₁.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X} (hf : IsLevelConstantS₁ S f) : IsLevelConstantS₁ S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

variable {S} in
lemma IsLevelConstantS₂.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) : IsLevelConstantS₂ S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

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

lemma mem_levelCochainsS₁_iff (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCochainsS₁ S M ↔ IsLevelConstantS₁ S f := Iff.rfl

lemma mem_levelCochainsS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCochainsS₂ S M ↔ IsLevelConstantS₂ S f := Iff.rfl

def levelCocyclesS₁ : Submodule k (cocycles₁ M) :=
  (levelCochainsS₁ S M).comap (cocycles₁ M).subtype

def continuousH1S : Submodule k (H1 M) :=
  (levelCocyclesS₁ S M).map (H1π M).hom

lemma mem_continuousH1S_iff (x : H1 M) :
    x ∈ continuousH1S S M ↔ ∃ c : cocycles₁ M, IsLevelConstantS₁ S c ∧ (H1π M).hom c = x := by
  simp only [continuousH1S, Submodule.mem_map, levelCocyclesS₁, Submodule.mem_comap]; rfl

lemma continuousH1S_le_continuousH1 : continuousH1S S M ≤ continuousH1 (MonoidHom.id _) M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1S_iff S M x).1 hx
  exact H1π_mem_continuousH1 _ M hc.isLevelConstant₁

variable {S} in

lemma continuousH1S_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH1S S M ≤ continuousH1S S' M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1S_iff S M x).1 hx
  exact (mem_continuousH1S_iff S' M _).2 ⟨c, hc.mono h, rfl⟩

def levelCocyclesS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :=
  cocycles₂ M ⊓ levelCochainsS₂ S M

def levelCoboundariesS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :=
  (levelCochainsS₁ S M).map (d₁₂ M).hom

lemma mem_levelCocyclesS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCocyclesS₂ S M ↔ f ∈ cocycles₂ M ∧ IsLevelConstantS₂ S f := Iff.rfl

lemma mem_levelCoboundariesS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCoboundariesS₂ S M ↔
      ∃ x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M, IsLevelConstantS₁ S x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundariesS₂, Submodule.mem_map, mem_levelCochainsS₁_iff]

lemma levelCocyclesS₂_le_levelCocycles₂ : levelCocyclesS₂ S M ≤ levelCocycles₂ (MonoidHom.id _) M :=
  fun _ h => ⟨h.1, h.2.isLevelConstant₂⟩

lemma levelCoboundariesS₂_le_levelCoboundaries₂ :
    levelCoboundariesS₂ S M ≤ levelCoboundaries₂ (MonoidHom.id _) M := by
  rintro f hf
  obtain ⟨x, hx, rfl⟩ := (mem_levelCoboundariesS₂_iff S M f).1 hf
  exact (mem_levelCoboundaries₂_iff _ M _).2 ⟨x, hx.isLevelConstant₁, rfl⟩

abbrev continuousH2S : Type :=
  ↥(levelCocyclesS₂ S M) ⧸ (levelCoboundariesS₂ S M).comap (levelCocyclesS₂ S M).subtype

abbrev continuousH2Sπ : ↥(levelCocyclesS₂ S M) →ₗ[k] continuousH2S S M :=
  Submodule.mkQ _

lemma continuousH2Sπ_eq_zero_iff (f : ↥(levelCocyclesS₂ S M)) :
    continuousH2Sπ S M f = 0 ↔
      (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
        ∈ levelCoboundariesS₂ S M := by
  simp [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

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

@[simp]
lemma locTotal₂S_apply (x : continuousH2S S M) (v : extArithIndex S) :
    locTotal₂S S M x v = locRes₂S S M (extArithLoc S v) x := rfl

noncomputable def sha₂ : Submodule k (continuousH2S S M) :=
  LinearMap.ker (locTotal₂S S M)

section Sha
variable {K : Type} [Field K] (A : Rep K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def sha₁ : Submodule K (H1 A) :=
  continuousH1S S A ⊓ LinearMap.ker (locTotal (extArithLoc S) A)

end Sha

end groupCohomology

end
