import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

open CategoryTheory Module

universe u

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

def twist (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, mul_smul, smul_mul_assoc, mul_smul_comm]

lemma twist_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) :
    ρ.twist χ g = (χ g : k) • ρ g := rfl

lemma twist_apply_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) (v : V) :
    ρ.twist χ g v = (χ g : k) • ρ g v := rfl

@[simp]
lemma twist_one (ρ : Representation k G V) : ρ.twist 1 = ρ := by
  ext g v
  simp [twist_apply_apply]

end Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev twist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.twist χ)

noncomputable abbrev dualTwist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.dual.twist χ)

lemma dualTwist_ρ_apply (A : Rep k G) (χ : G →* kˣ) (g : G) (f : Module.Dual k A) :
    (A.dualTwist χ).ρ g f = (χ g : k) • (f ∘ₗ A.ρ g⁻¹) := rfl

lemma finrank_dualTwist (k : Type u) [Field k] {G : Type u} [Group G] (A : Rep k G)
    (χ : G →* kˣ) [FiniteDimensional k A] :
    finrank k (A.dualTwist χ) = finrank k A :=
  Subspace.dual_finrank_eq

end Rep

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable abbrev locRes (v : ι) : H1 M ⟶ H1 (Rep.res (loc v) M) :=
  map (loc v) (𝟙 (Rep.res (loc v) M)) 1

noncomputable def selmer (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    Submodule k (H1 M) :=
  ⨅ v, (L v).comap (locRes loc M v).hom

omit [Fintype ι] in
lemma mem_selmer_iff (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (x : H1 M) :
    x ∈ selmer loc M L ↔ ∀ v, (locRes loc M v).hom x ∈ L v := by
  simp [selmer, Submodule.mem_iInf]

omit [Fintype ι] in

lemma selmer_mono {L L' : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : ∀ v, L v ≤ L' v) : selmer loc M L ≤ selmer loc M L' :=
  iInf_mono fun v => Submodule.comap_mono (h v)

omit [Fintype ι] in

lemma selmer_bot_le (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmer loc M (fun _ => ⊥) ≤ selmer loc M L :=
  selmer_mono loc M fun _ => bot_le

omit [Fintype ι] in

lemma subsingleton_selmer_of_subsingleton (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    [Subsingleton (H1 M)] : Subsingleton (selmer loc M L) :=
  inferInstance

def orthogonal {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (B : V →ₗ[k] W →ₗ[k] k) (L : Submodule k V) : Submodule k W :=
  L.dualAnnihilator.comap B.flip

@[simp]
lemma mem_orthogonal_iff {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) (L : Submodule k V) (w : W) :
    w ∈ orthogonal B L ↔ ∀ x ∈ L, B x w = 0 := by
  simp only [orthogonal, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  exact forall₂_congr fun x _ => by rw [LinearMap.flip_apply]

@[simp]
lemma orthogonal_bot {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) : orthogonal B (⊥ : Submodule k V) = ⊤ := by
  ext w
  simp only [mem_orthogonal_iff, Submodule.mem_top, iff_true]
  rintro x rfl
  simp

lemma orthogonal_anti {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) {L L' : Submodule k V} (h : L ≤ L') :
    orthogonal B L' ≤ orthogonal B L :=
  Submodule.comap_mono (Submodule.dualAnnihilator_anti h)

variable (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

noncomputable def dualConditions (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (v : ι) :
    Submodule k (H1 (Rep.res (loc v) M')) :=
  orthogonal (pairing v) (L v)

def greenbergWilesEq (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  finrank k (selmer loc M L)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    = finrank k (selmer loc M' (dualConditions loc M M' pairing L))
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

structure IsGreenbergWilesDatum (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop where

  finite_selmer : FiniteDimensional k (selmer loc M L)

  finite_dualSelmer :
    FiniteDimensional k (selmer loc M' (dualConditions loc M M' pairing L))

  finite_local : ∀ v, FiniteDimensional k (L v)

  formula : greenbergWilesEq loc M M' pairing L

theorem finrank_selmer_le_of_isGreenbergWilesDatum
    {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesDatum loc M M' pairing L) :
    finrank k (selmer loc M L)
      ≤ finrank k (selmer loc M' (dualConditions loc M M' pairing L))
        + finrank k M.ρ.invariants + ∑ v, finrank k (L v) := by
  have := h.formula
  unfold greenbergWilesEq at this
  omega

def localTermBalanced (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  ∀ v, finrank k (L v) = finrank k (Rep.res (loc v) M).ρ.invariants

end groupCohomology
