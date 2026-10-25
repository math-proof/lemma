import Mathlib
import Lemma.Compat.Mathlib430
import Abbrev.GroupCohomology_SplittingModule

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

section Augmentation

variable (k G : Type u) [CommRing k] [Group G]

def augShortComplex : ShortComplex (Rep k G) where
  X₁ := augIdeal k G
  X₂ := Rep.leftRegularFinsupp k G
  X₃ := Rep.trivial k G k
  f := augIdealι k G
  g := augε k G
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

@[simp] lemma augShortComplex_X₁ : (augShortComplex k G).X₁ = augIdeal k G := rfl
@[simp] lemma augShortComplex_X₂ : (augShortComplex k G).X₂ = Rep.leftRegularFinsupp k G := rfl
@[simp] lemma augShortComplex_X₃ : (augShortComplex k G).X₃ = Rep.trivial k G k := rfl
@[simp] lemma augShortComplex_f : (augShortComplex k G).f = augIdealι k G := rfl
@[simp] lemma augShortComplex_g : (augShortComplex k G).g = augε k G := rfl

variable {k G}

lemma augε_hom_apply (f : G →₀ k) : (augε k G).hom f = Finsupp.linearCombination k (fun _ : G => (1 : k)) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single g r => rw [Rep.leftRegularHomFinsupp_hom_single, Finsupp.linearCombination_single]; rfl

lemma mem_augIdeal_iff (f : G →₀ k) :
    f ∈ LinearMap.ker (augε k G).hom.toLinearMap ↔ Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0 := by
  rw [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply, augε_hom_apply]

lemma coe_augIdeal_ρ_apply (σ : G) (f : augIdeal k G) : ((augIdeal k G).ρ σ f : G →₀ k) = Finsupp.lmapDomain k k (σ * ·) (f : G →₀ k) := rfl

end Augmentation

section Splitting

variable {k G : Type u} [CommRing k] [Group G] (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C)

def cocycleTwist (σ : G) : (G →₀ k) →ₗ[k] C :=
  Finsupp.linearCombination k (fun τ : G => (φ : G × G → C) (σ, τ))

@[simp] lemma cocycleTwist_single (σ τ : G) (r : k) :
    cocycleTwist C φ σ (Finsupp.single τ r) = r • (φ : G × G → C) (σ, τ) := by
  rw [cocycleTwist, Finsupp.linearCombination_single]

lemma cocycleTwist_apply (σ : G) (f : G →₀ k) :
    cocycleTwist C φ σ f = f.sum fun τ r => r • (φ : G × G → C) (σ, τ) :=
  Finsupp.linearCombination_apply _ _

lemma cocycles₂_one_left (τ : G) : (φ : G × G → C) (1, τ) = (φ : G × G → C) (1, 1) := by
  have h := (groupCohomology.mem_cocycles₂_iff (φ : G × G → C)).1 φ.2 1 1 τ
  rw [one_mul, one_mul, map_one] at h
  change (φ : G × G → C) (1, τ) + (φ : G × G → C) (1, 1) = (φ : G × G → C) (1, τ) + (φ : G × G → C) (1, τ) at h
  exact (add_left_cancel h).symm

lemma cocycleTwist_one (f : G →₀ k) (hf : Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0) :
    cocycleTwist C φ 1 f = 0 := by
  rw [cocycleTwist_apply, Finsupp.sum, Finset.sum_congr rfl fun τ _ => by rw [cocycles₂_one_left C φ τ], ← Finset.sum_smul]
  change (f.sum fun _ r => r) • (φ : G × G → C) (1, 1) = 0
  rw [show (f.sum fun _ r => r) = Finsupp.linearCombination k (fun _ : G => (1 : k)) f by
    simp [Finsupp.linearCombination_apply], hf, zero_smul]

lemma cocycleTwist_mul (σ σ' : G) (f : G →₀ k) (hf : Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0) :
    cocycleTwist C φ (σ * σ') f = C.ρ σ (cocycleTwist C φ σ' f) + cocycleTwist C φ σ (Finsupp.lmapDomain k k (σ' * ·) f) := by
  have hx : ∀ g h l : G, (φ : G × G → C) (g * h, l) + (φ : G × G → C) (g, h) =
      C.ρ g ((φ : G × G → C) (h, l)) + (φ : G × G → C) (g, h * l) :=
    (groupCohomology.mem_cocycles₂_iff (φ : G × G → C)).1 φ.2
  have h2 : cocycleTwist C φ σ (Finsupp.lmapDomain k k (σ' * ·) f) = f.sum fun τ r => r • (φ : G × G → C) (σ, σ' * τ) := by
    rw [cocycleTwist, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    rfl
  rw [h2, cocycleTwist_apply, cocycleTwist_apply]
  simp only [Finsupp.sum]
  rw [map_sum, ← Finset.sum_add_distrib]
  have h3 : ∀ τ, f τ • (φ : G × G → C) (σ * σ', τ) + f τ • (φ : G × G → C) (σ, σ') =
      C.ρ σ (f τ • (φ : G × G → C) (σ', τ)) + f τ • (φ : G × G → C) (σ, σ' * τ) := fun τ => by
    rw [map_smul, ← smul_add, ← smul_add, hx σ σ' τ]
  rw [← Finset.sum_congr rfl fun τ _ => h3 τ, Finset.sum_add_distrib, ← Finset.sum_smul]
  change _ = _ + (f.sum fun _ r => r) • (φ : G × G → C) (σ, σ')
  rw [show (f.sum fun _ r => r) = Finsupp.linearCombination k (fun _ : G => (1 : k)) f by
    simp [Finsupp.linearCombination_apply], hf, zero_smul, add_zero]

def splittingRep : Representation k G (C × augIdeal k G) where
  toFun σ := LinearMap.prod
    (C.ρ σ ∘ₗ LinearMap.fst k C (augIdeal k G) +
      cocycleTwist C φ σ ∘ₗ (LinearMap.ker (augε k G).hom.toLinearMap).subtype ∘ₗ LinearMap.snd k C (augIdeal k G))
    ((augIdeal k G).ρ σ ∘ₗ LinearMap.snd k C (augIdeal k G))
  map_one' := LinearMap.ext fun v => Prod.ext
    (by
      change C.ρ 1 v.1 + cocycleTwist C φ 1 (v.2 : G →₀ k) = v.1
      rw [map_one, cocycleTwist_one C φ _ ((mem_augIdeal_iff _).1 v.2.2), add_zero]; rfl)
    (by change (augIdeal k G).ρ 1 v.2 = v.2; rw [map_one]; rfl)
  map_mul' σ σ' := LinearMap.ext fun v => Prod.ext
    (by
      change C.ρ (σ * σ') v.1 + cocycleTwist C φ (σ * σ') (v.2 : G →₀ k) =
        C.ρ σ (C.ρ σ' v.1 + cocycleTwist C φ σ' (v.2 : G →₀ k)) + cocycleTwist C φ σ (((augIdeal k G).ρ σ' v.2 : augIdeal k G) : G →₀ k)
      rw [map_mul, map_add, cocycleTwist_mul C φ σ σ' _ ((mem_augIdeal_iff _).1 v.2.2), add_assoc, coe_augIdeal_ρ_apply]; rfl)
    (by change (augIdeal k G).ρ (σ * σ') v.2 = (augIdeal k G).ρ σ ((augIdeal k G).ρ σ' v.2); rw [map_mul]; rfl)

abbrev splittingModule : Rep k G := Rep.of (splittingRep C φ)

lemma splittingModule_ρ_apply (σ : G) (v : C × augIdeal k G) :
    (splittingModule C φ).ρ σ v = (C.ρ σ v.1 + cocycleTwist C φ σ (v.2 : G →₀ k), (augIdeal k G).ρ σ v.2) := rfl

def splittingModuleι : C ⟶ splittingModule C φ :=
  Rep.ofHom ⟨LinearMap.inl k C (augIdeal k G), fun σ => LinearMap.ext fun c => Prod.ext
    (by change C.ρ σ c = C.ρ σ c + cocycleTwist C φ σ ((0 : augIdeal k G) : G →₀ k); rw [ZeroMemClass.coe_zero, map_zero, add_zero])
    (by change (0 : augIdeal k G) = (augIdeal k G).ρ σ 0; rw [map_zero])⟩

def splittingModuleπ : splittingModule C φ ⟶ augIdeal k G :=
  Rep.ofHom ⟨LinearMap.snd k C (augIdeal k G), fun _ => LinearMap.ext fun _ => rfl⟩

@[simp] lemma splittingModuleι_hom_apply (c : C) : (splittingModuleι C φ).hom c = ((c, 0) : C × augIdeal k G) := rfl
@[simp] lemma splittingModuleπ_hom_apply (v : C × augIdeal k G) : (splittingModuleπ C φ).hom v = v.2 := rfl

def splittingShortComplex : ShortComplex (Rep k G) where
  X₁ := C
  X₂ := splittingModule C φ
  X₃ := augIdeal k G
  f := splittingModuleι C φ
  g := splittingModuleπ C φ
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

@[simp] lemma splittingShortComplex_X₁ : (splittingShortComplex C φ).X₁ = C := rfl
@[simp] lemma splittingShortComplex_X₂ : (splittingShortComplex C φ).X₂ = splittingModule C φ := rfl
@[simp] lemma splittingShortComplex_X₃ : (splittingShortComplex C φ).X₃ = augIdeal k G := rfl
@[simp] lemma splittingShortComplex_f : (splittingShortComplex C φ).f = splittingModuleι C φ := rfl
@[simp] lemma splittingShortComplex_g : (splittingShortComplex C φ).g = splittingModuleπ C φ := rfl

end Splitting

end Rep

end
