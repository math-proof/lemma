module

public import Theorem.Scheme.OrderedAffineCoverCech
public import Theorem.Scheme.OrderedAffineCoverCechCup
public import Theorem.Scheme.OrderedAffineCoverCochainPullback

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)


public theorem inter_eq_ointer {n : ℕ} (s : K.Idx n) : K.inter s = K.ointer s.1 := rfl


public theorem ointer_le {n : ℕ} (t : K.OIdx n) (j : Fin (n + 1)) : K.ointer t ≤ K.U (t j) := iInf_le _ j


public theorem oface_apply {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    K.oface t j k = t (j.succAbove k) := rfl


public theorem ointer_le_ointer_oface {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) :
    K.ointer t ≤ K.ointer (K.oface t j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)


public theorem ofrontFace_apply (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) (j : Fin (a + 1)) :
    K.ofrontFace a b n h t j = t ⟨j.1, by omega⟩ := rfl


public theorem obackFace_apply (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) (j : Fin (b + 1)) :
    K.obackFace a b n h t j = t ⟨a + j.1, by omega⟩ := rfl


public theorem frontFace_val (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    (K.frontFace a b n h s).1 = K.ofrontFace a b n h s.1 := rfl


public theorem backFace_val (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    (K.backFace a b n h s).1 = K.obackFace a b n h s.1 := rfl


public theorem ointer_le_ointer_ofrontFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) :
    K.ointer t ≤ K.ointer (K.ofrontFace a b n h t) :=
  le_iInf fun _ => iInf_le _ _


public theorem ointer_le_ointer_obackFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) :
    K.ointer t ≤ K.ointer (K.obackFace a b n h t) :=
  le_iInf fun _ => iInf_le _ _


public theorem osort_val {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    (K.osort t hinj).1 = t ∘ Tuple.sort t := rfl


public theorem ointer_le_inter_osort {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    K.ointer t ≤ K.inter (K.osort t hinj) :=
  le_iInf fun j => iInf_le _ (Tuple.sort t j)


public theorem inter_osort_le_ointer {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    K.inter (K.osort t hinj) ≤ K.ointer t :=
  le_iInf fun j => (iInf_le _ ((Tuple.sort t).symm j)).trans (by
    change K.U (t (Tuple.sort t ((Tuple.sort t).symm j))) ≤ K.U (t j)
    rw [Equiv.apply_symm_apply])


public theorem ointer_le_preimage_ointer_comp {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover)
    (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    {n : ℕ} (t : 𝒲.OIdx n) : 𝒲.ointer t ≤ h ⁻¹ᵁ 𝒦.ointer (lam ∘ t) := by
  change 𝒲.ointer t ≤ h ⁻¹ᵁ (⨅ j, 𝒦.U (lam (t j)))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  exact le_iInf fun j => (iInf_le (fun i => 𝒲.U (t i)) j).trans (hlam _)

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)


public theorem od_apply (n : ℕ) (c : F.ocochain K n) (t : K.OIdx (n + 1)) :
    F.od K n c t = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.res (K.ointer_le_ointer_oface t j) (c (K.oface t j)) := by
  simp only [od, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]


public theorem ocup_apply (a b n : ℕ) (h : a + b = n) (α : (unit π).ocochain K a) (β : F.ocochain K b) (t : K.OIdx n) :
    F.ocup K a b n h α β t =
      (V.presheaf.map (homOfLE (K.ointer_le_ointer_ofrontFace a b n h t)).op).hom (α (K.ofrontFace a b n h t))
        • F.res (K.ointer_le_ointer_obackFace a b n h t) (β (K.obackFace a b n h t)) :=
  rfl


public theorem ores_apply (n : ℕ) (c : F.ocochain K n) (s : K.Idx n) : F.ores K n c s = c s.1 := rfl


public theorem oext_apply_of_injective (n : ℕ) (z : F.cochain K n) (t : K.OIdx n) (hinj : Function.Injective t) :
    F.oext K n z t = ((Equiv.Perm.sign (Tuple.sort t) : ℤˣ) : ℤ) •
      F.res (K.ointer_le_inter_osort t hinj) (z (K.osort t hinj)) := by
  classical
  simp [oext, LinearMap.pi_apply, hinj, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]


public theorem oext_apply_of_not_injective (n : ℕ) (z : F.cochain K n) (t : K.OIdx n) (hinj : ¬ Function.Injective t) :
    F.oext K n z t = 0 := by
  classical
  simp [oext, LinearMap.pi_apply, hinj, LinearMap.zero_apply]

variable {R' : Type u} [CommRing R'] {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}


public theorem ounitPullback_apply (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (c : (unit πY).ocochain 𝒦 n) (t : 𝒲.OIdx n) :
    ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n c t =
      (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).op).hom
        ((h.app (𝒦.ointer (lam ∘ t))).hom (c (lam ∘ t))) :=
  rfl

end OModulePresheaf

end AlgebraicGeometry

end
