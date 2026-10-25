import Mathlib

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

variable {r} in
lemma IsLevelConstant₁.add {X : Type*} [Add X] {f f' : G → X}
    (hf : IsLevelConstant₁ r f) (hf' : IsLevelConstant₁ r f') : IsLevelConstant₁ r (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  haveI := hF; haveI := hF'
  refine ⟨F ⊔ F', inferInstance, fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

variable {r} in
lemma IsLevelConstant₂.add {X : Type*} [Add X] {f f' : G × G → X}
    (hf : IsLevelConstant₂ r f) (hf' : IsLevelConstant₂ r f') : IsLevelConstant₂ r (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  haveI := hF; haveI := hF'
  refine ⟨F ⊔ F', inferInstance, fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.add_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

lemma isLevelConstant₁_const {X : Type*} (x : X) : IsLevelConstant₁ r (fun _ : G => x) :=
  ⟨⊥, inferInstance, fun _ _ _ => rfl⟩

lemma isLevelConstant₂_const {X : Type*} (x : X) : IsLevelConstant₂ r (fun _ : G × G => x) :=
  ⟨⊥, inferInstance, fun _ _ _ _ _ _ => rfl⟩

variable {r} in
lemma IsLevelConstant₁.comp {X Y : Type*} {f : G → X} (hf : IsLevelConstant₁ r f) (φ : X → Y) :
    IsLevelConstant₁ r (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

variable {r} in
lemma IsLevelConstant₂.comp {X Y : Type*} {f : G × G → X} (hf : IsLevelConstant₂ r f) (φ : X → Y) :
    IsLevelConstant₂ r (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩

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

lemma mem_levelCochains₁_iff (f : G → M) : f ∈ levelCochains₁ r M ↔ IsLevelConstant₁ r f :=
  Iff.rfl

lemma mem_levelCochains₂_iff (f : G × G → M) : f ∈ levelCochains₂ r M ↔ IsLevelConstant₂ r f :=
  Iff.rfl

def levelCocycles₂ : Submodule k (G × G → M) :=
  cocycles₂ M ⊓ levelCochains₂ r M

lemma mem_levelCocycles₂_iff (f : G × G → M) :
    f ∈ levelCocycles₂ r M ↔ f ∈ cocycles₂ M ∧ IsLevelConstant₂ r f :=
  Iff.rfl

def levelCoboundaries₂ : Submodule k (G × G → M) :=
  (levelCochains₁ r M).map (d₁₂ M).hom

lemma mem_levelCoboundaries₂_iff (f : G × G → M) :
    f ∈ levelCoboundaries₂ r M ↔ ∃ x : G → M, IsLevelConstant₁ r x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundaries₂, Submodule.mem_map, mem_levelCochains₁_iff]

lemma levelCoboundaries₂_le_coboundaries₂ : levelCoboundaries₂ r M ≤ coboundaries₂ M :=
  fun _ ⟨x, _, hx⟩ => ⟨x, hx⟩

lemma levelCoboundaries₂_le_cocycles₂ : levelCoboundaries₂ r M ≤ cocycles₂ M :=
  (levelCoboundaries₂_le_coboundaries₂ r M).trans (coboundaries₂_le_cocycles₂ M)

lemma levelCocycles₂_le_cocycles₂ : levelCocycles₂ r M ≤ cocycles₂ M :=
  inf_le_left

abbrev continuousH2 : Type u :=
  ↥(levelCocycles₂ r M) ⧸ (levelCoboundaries₂ r M).comap (levelCocycles₂ r M).subtype

abbrev continuousH2π : ↥(levelCocycles₂ r M) →ₗ[k] continuousH2 r M :=
  Submodule.mkQ _

lemma continuousH2π_eq_zero_iff (f : ↥(levelCocycles₂ r M)) :
    continuousH2π r M f = 0 ↔ (f : G × G → M) ∈ levelCoboundaries₂ r M := by
  simp [continuousH2π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

def levelCocyclesToCocycles₂ : ↥(levelCocycles₂ r M) →ₗ[k] ↥(cocycles₂ M) where
  toFun c := ⟨(c : G × G → M), c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def continuousH2ToH2 : continuousH2 r M →ₗ[k] H2 M :=
  Submodule.liftQ _ ((H2π M).hom ∘ₗ levelCocyclesToCocycles₂ r M)
    (fun c hc => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact (H2π_eq_zero_iff _).2 (levelCoboundaries₂_le_coboundaries₂ r M hc))

@[simp]
lemma continuousH2ToH2_mk (c : ↥(levelCocycles₂ r M)) :
    continuousH2ToH2 r M (Submodule.Quotient.mk c) = H2π M (levelCocyclesToCocycles₂ r M c) :=
  rfl

end groupCohomology
