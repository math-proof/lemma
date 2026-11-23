module

public import Mathlib
public import Structure.GroupCohomology_CupProduct

public section

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]


public theorem ρ_mul_apply (M : Rep k G) (s t : G) (x : M) :
    M.ρ (s * t) x = M.ρ s (M.ρ t x) := by
  rw [Rep.ρ_mul]; rfl

variable (φ : A →ₗ[k] B →ₗ[k] N)


@[simp]
public theorem cupCochain_apply (f : G → A) (g : G → B) (s t : G) :
    cupCochain φ f g (s, t) = φ (f s) (B.ρ s (g t)) := rfl

variable (hφ : Rep.IsEquivariantBilinear A B N φ)

include hφ in


public theorem cupCochain_mem_cocycles₂ (f : cocycles₁ A) (g : cocycles₁ B) :
    cupCochain φ (⇑f) (⇑g) ∈ cocycles₂ N := by
  rw [mem_cocycles₂_iff]
  intro s t u
  simp only [cupCochain_apply]

  rw [(mem_cocycles₁_iff (⇑f)).1 f.2 s t, (mem_cocycles₁_iff (⇑g)).1 g.2 t u,
    ← hφ s (f t) (B.ρ t (g u))]
  simp only [map_add, LinearMap.add_apply, ρ_mul_apply]
  abel


@[simp]
public theorem cup_apply (f : cocycles₁ A) (g : cocycles₁ B) (s t : G) :
    (cup φ hφ f g) (s, t) = φ (f s) (B.ρ s (g t)) := rfl


public theorem cup_coe (f : cocycles₁ A) (g : cocycles₁ B) :
    ⇑(cup φ hφ f g) = cupCochain φ (⇑f) (⇑g) := rfl

include hφ in


public theorem cup_mem_coboundaries₂_left {f : cocycles₁ A} (hf : ⇑f ∈ coboundaries₁ A)
    (g : cocycles₁ B) : ⇑(cup φ hφ f g) ∈ coboundaries₂ N := by
  obtain ⟨a, ha⟩ := hf
  have hfs : ∀ s : G, f s = A.ρ s a - a := fun s => by rw [← ha, d₀₁_hom_apply]
  refine ⟨fun t => φ a (g t), funext fun p => ?_⟩
  obtain ⟨s, t⟩ := p
  rw [d₁₂_hom_apply]
  show N.ρ s (φ a (g t)) - φ a (g (s * t)) + φ a (g s) = φ (f s) (B.ρ s (g t))
  rw [hfs s, (mem_cocycles₁_iff (⇑g)).1 g.2 s t, ← hφ s a (g t)]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  abel

include hφ in


public theorem cup_mem_coboundaries₂_right (f : cocycles₁ A) {g : cocycles₁ B}
    (hg : ⇑g ∈ coboundaries₁ B) : ⇑(cup φ hφ f g) ∈ coboundaries₂ N := by
  obtain ⟨b, hb⟩ := hg
  have hgs : ∀ t : G, g t = B.ρ t b - b := fun t => by rw [← hb, d₀₁_hom_apply]
  rw [← neg_mem_iff]
  refine ⟨fun s => φ (f s) (B.ρ s b), funext fun p => ?_⟩
  obtain ⟨s, t⟩ := p
  rw [d₁₂_hom_apply]
  show N.ρ s (φ (f t) (B.ρ t b)) - φ (f (s * t)) (B.ρ (s * t) b) + φ (f s) (B.ρ s b)
      = -(φ (f s) (B.ρ s (g t)))
  rw [hgs t, (mem_cocycles₁_iff (⇑f)).1 f.2 s t, ← hφ s (f t) (B.ρ t b),
    ρ_mul_apply B s t b]
  simp only [map_add, map_sub, LinearMap.add_apply]
  abel

section DescentGadget

variable {W : Type u} [AddCommGroup W] [Module k W]

variable (A) in


public theorem H1π_surjective : Function.Surjective (H1π A).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance


public theorem H1_hom_ext {F F' : H1 A →ₗ[k] W}
    (h : ∀ x : cocycles₁ A, F (H1π A x) = F' (H1π A x)) : F = F' :=
  LinearMap.ext fun y => H1_induction_on y h


@[simp]
public theorem H1desc_H1π (F : cocycles₁ A →ₗ[k] W)
    (hF : ∀ x : cocycles₁ A, ⇑x ∈ coboundaries₁ A → F x = 0) (x : cocycles₁ A) :
    H1desc F hF (H1π A x) = F x := by
  unfold H1desc
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

end DescentGadget


public theorem cupRight_H1π (f : cocycles₁ A) (g : cocycles₁ B) :
    cupRight φ hφ f (H1π B g) = H2π N (cup φ hφ f g) :=
  H1desc_H1π _ _ g

