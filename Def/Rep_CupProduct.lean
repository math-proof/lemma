module

public import Mathlib
public import Structure.GroupCohomology_CupProduct

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

def IsEquivariantBilinear (A B N : Rep k G) (φ : A →ₗ[k] B →ₗ[k] N) : Prop :=
  ∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)

end Rep

namespace groupCohomology

section CupProduct

variable {k G : Type u} [CommRing k] [Group G] {A B N : Rep k G}

variable (φ : A →ₗ[k] B →ₗ[k] N)

def cupCochain (f : G → A) (g : G → B) : G × G → N :=
  fun p => φ (f p.1) (B.ρ p.1 (g p.2))

variable (hφ : Rep.IsEquivariantBilinear A B N φ)

include hφ in

noncomputable def cup : cocycles₁ A →ₗ[k] cocycles₁ B →ₗ[k] cocycles₂ N :=
  LinearMap.mk₂ k
    (fun f g => ⟨cupCochain φ (⇑f) (⇑g), cupCochain_mem_cocycles₂ φ hφ f g⟩)
    (fun f f' g => by
      ext s t
      show φ (f s + f' s) (B.ρ s (g t)) = φ (f s) (B.ρ s (g t)) + φ (f' s) (B.ρ s (g t))
      rw [map_add, LinearMap.add_apply])
    (fun c f g => by
      ext s t
      show φ (c • f s) (B.ρ s (g t)) = c • φ (f s) (B.ρ s (g t))
      rw [map_smul, LinearMap.smul_apply])
    (fun f g g' => by
      ext s t
      show φ (f s) (B.ρ s (g t + g' t)) = φ (f s) (B.ρ s (g t)) + φ (f s) (B.ρ s (g' t))
      rw [map_add, map_add])
    (fun c f g => by
      ext s t
      show φ (f s) (B.ρ s (c • g t)) = c • φ (f s) (B.ρ s (g t))
      rw [map_smul, map_smul])

section DescentGadget

variable {W : Type u} [AddCommGroup W] [Module k W]

variable (A) in

noncomputable def H1desc (F : cocycles₁ A →ₗ[k] W)
    (hF : ∀ x : cocycles₁ A, ⇑x ∈ coboundaries₁ A → F x = 0) : H1 A →ₗ[k] W :=
  (LinearMap.ker (H1π A).hom).liftQ F
      (fun x hx => LinearMap.mem_ker.2
        (hF x ((H1π_eq_zero_iff x).1 (LinearMap.mem_ker.1 hx)))) ∘ₗ
    ((H1π A).hom.quotKerEquivOfSurjective (H1π_surjective A)).symm.toLinearMap

end DescentGadget

private noncomputable def cupRight (f : cocycles₁ A) : H1 B →ₗ[k] H2 N :=
  H1desc ((H2π N).hom ∘ₗ cup φ hφ f)
    (fun _ hg => (H2π_eq_zero_iff _).2 (cup_mem_coboundaries₂_right φ hφ f hg))

noncomputable def cupH1 : H1 A →ₗ[k] H1 B →ₗ[k] H2 N :=
  H1desc
    { toFun := cupRight φ hφ
      map_add' := fun f f' => H1_hom_ext fun g =>
        ((cupRight_H1π φ hφ (f + f') g).trans (by
            rw [map_add, LinearMap.add_apply, map_add])).trans
          (congrArg₂ (· + ·) (cupRight_H1π φ hφ f g) (cupRight_H1π φ hφ f' g)).symm
      map_smul' := fun c f => H1_hom_ext fun g =>
        ((cupRight_H1π φ hφ (c • f) g).trans (by
            rw [map_smul, LinearMap.smul_apply, map_smul])).trans
          (congrArg (c • ·) (cupRight_H1π φ hφ f g)).symm }
    (fun f hf => H1_hom_ext fun g =>
      (cupRight_H1π φ hφ f g).trans
        ((H2π_eq_zero_iff _).2 (cup_mem_coboundaries₂_left φ hφ hf g)))


end CupProduct

section Arithmetic

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def IsLocalTatePairingFamily : Prop :=
  ∀ v : ι, ∃ (Nv : Rep k (Γv v))
    (φv : Rep.res (loc v) M →ₗ[k] Rep.res (loc v) M' →ₗ[k] Nv)
    (hφv : Rep.IsEquivariantBilinear _ _ _ φv) (invv : H2 Nv →ₗ[k] k),
      IsLocalTateDatum φv hφv invv (pairing v)

end Arithmetic


section Family

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def IsLocalTateDualityFamily : Prop :=
  ∀ v : ι, ∃ (Nv : Rep k (Γv v))
    (φv : Rep.res (loc v) M →ₗ[k] Rep.res (loc v) M' →ₗ[k] Nv)
    (hφv : Rep.IsEquivariantBilinear _ _ _ φv) (invv : H2 Nv →ₗ[k] k),
      IsLocalTateDuality φv hφv invv (pairing v)

end Family

end groupCohomology

end
