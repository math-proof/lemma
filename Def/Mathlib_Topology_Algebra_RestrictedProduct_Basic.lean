import Mathlib

section


open RestrictedProduct

section modules

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : Filter.Tendsto f 𝓕₂ 𝓕₁)
variable {A : Type*} [Semiring A]
variable [Π i, AddCommMonoid (R₁ i)] [Π i, AddCommMonoid (R₂ i)] [Π i, Module A (R₁ i)]
    [Π i, Module A (R₂ i)] [∀ i, AddSubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, AddSubmonoidClass (S₂ i) (R₂ i)] [∀ i, SMulMemClass (S₁ i) A (R₁ i)]
    [∀ i, SMulMemClass (S₂ i) A (R₂ i)]
    (φ : ∀ j, R₁ (f j) →ₗ[A] R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, Set.MapsTo (φ j) (B₁ (f j)) (B₂ j))

def RestrictedProduct.mapAlongLinearMap :
    Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  map_smul' a f := by
    ext i
    apply map_smul (φ i)


variable (A : Type*) [CommRing A] {ι : Type*} (R : ι → Type*)
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] (C : ∀ i, Submodule A (R i))

def RestrictedProduct.inclusionLinearMap
     {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕] :=
  mapAlongLinearMap R R id h (fun _ ↦ .id)
  (Filter.Eventually.of_forall <| fun _ _ ↦ id)

end modules

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

namespace RestrictedProduct

section supports

variable {S T : ι → Type*}
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [(i : ι) → One (G i)] in

@[to_additive

                                                                  ]
def mulSupport (u : Πʳ i, [G i, A i]) : Set ι :=
  {i : ι | u i ≠ 1}


variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubmonoidClass T (Πʳ i, [G i, A i])] in

def SubmonoidClass.isProductAt (U : T) (i : ι) : Prop :=
  ∀ u ∈ U, ∃ uᵢ, uᵢ ∈ U ∧ ∃ uᵢ', uᵢ' ∈ U ∧ u = uᵢ * uᵢ' ∧ mulSupport uᵢ ⊆ {i} ∧ i ∉ mulSupport uᵢ'

variable [(i : ι) → Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubgroupClass T (Πʳ i, [G i, A i])] in

noncomputable
def indexSupport (u : Πʳ i, [G i, A i]) : Finset ι :=
  Set.Finite.toFinset (s := {x | u x ∉ A x}) (by have h := u.2; simp at h; exact h)

end supports


section structure_map

@[to_additive
                                                                                     ]
def structureMapMonoidHom {ι : Type*} (M : ι → Type*) [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →* Πʳ (i : ι), [M i, Submonoid.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_one' := rfl
  map_mul' := by intros; rfl

def structureMapRingHom {ι : Type*} (M : ι → Type*) [(i : ι) → Ring (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubringClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →+* Πʳ (i : ι), [M i, Subring.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by intros; rfl
  map_add' := by intros; rfl

def structureSubring {ι : Type*} (R : ι → Type*) {S : ι → Type*}
    (A : (i : ι) → (S i)) (𝓕 : Filter ι) [(i : ι) → SetLike (S i) (R i)] [(i : ι) → Ring (R i)]
    [(i : ι) → SubringClass (S i) (R i)] :
    Subring (Πʳ i, [R i, A i]_[𝓕]) :=
  (RestrictedProduct.structureMapRingHom R A 𝓕).range

end structure_map

end RestrictedProduct

end
