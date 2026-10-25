import Def.HeckeGalois_EichlerShimura
import Abbrev.ModularCurve_EigenformIdeal

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section TateModule

variable (p : ℕ) {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

def TateModule : Submodule HeckeAlg (ℕ → J) where
  carrier := {x | x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp only [Pi.add_apply, smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => smul_zero p⟩
  smul_mem' := by
    rintro s x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp only [Pi.smul_apply]
    rw [smul_comm, hx n]


section FreeOfRankTwo

variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]

def FreeOfRankTwo : Prop :=
  ∃ e₁ e₂ : ℕ → J, e₁ ∈ TateModule p J ∧ e₂ ∈ TateModule p J ∧
    (∀ t ∈ TateModule p J, ∃ (k : ℕ) (s₁ s₂ : HeckeAlg), p ^ k • t = s₁ • e₁ + s₂ • e₂) ∧
    (∀ s₁ s₂ : HeckeAlg, s₁ • e₁ + s₂ • e₂ = 0 →
      (∀ t ∈ TateModule p J, s₁ • t = 0) ∧ (∀ t ∈ TateModule p J, s₂ • t = 0))

def CardinalityAJ (g : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card {x : J // p ^ n • x = 0} = p ^ (2 * g * n)

end FreeOfRankTwo


section Torsion

variable (p : ℕ) {J : Type*} [AddCommGroup J]

def IsPPowTorsion (x : J) : Prop := ∃ n : ℕ, p ^ n • x = 0

end Torsion


section AttachmentData

variable {k : Type*} [Field k]

def attachmentTraceData (φ : HeckeAlg →+* k) : ℕ → k := fun ℓ =>
  if h : ℓ.Prime then φ (heckeGen ⟨ℓ, h⟩) else 0

def attachmentDetData (k : Type*) [Field k] : ℕ → k := fun ℓ => (ℓ : k)

end AttachmentData

end ModularCurve

end

end
