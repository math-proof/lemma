import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Lemma.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)

def sortIdx {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) : 𝒦.Idx n :=
  ⟨(lam ∘ s.1) ∘ (Tuple.sort (lam ∘ s.1)),
    (Tuple.monotone_sort (lam ∘ s.1)).strictMono_of_injective (hinj.comp (Tuple.sort (lam ∘ s.1)).injective)⟩

theorem sortIdx_val {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    (𝒲.sortIdx 𝒦 lam s hinj).1 = (lam ∘ s.1) ∘ (Tuple.sort (lam ∘ s.1)) :=
  rfl

theorem inter_le_preimage_inter_sortIdx (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    {n : ℕ} (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    𝒲.inter s ≤ h ⁻¹ᵁ 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj) := by
  change 𝒲.inter s ≤ h ⁻¹ᵁ (⨅ j, 𝒦.U ((𝒲.sortIdx 𝒦 lam s hinj).1 j))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  refine le_iInf fun j => ?_
  exact (iInf_le (fun i => 𝒲.U (s.1 i)) (Tuple.sort (lam ∘ s.1) j)).trans (hlam _)

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}

def unitPullback (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) : (unit πX).cochain 𝒲 n :=
  fun s => by
    classical
    exact if hinj : Function.Injective (lam ∘ s.1) then
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom
          ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj)))
    else 0

theorem unitPullback_apply_of_injective (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) (s : 𝒲.Idx n) (hinj : Function.Injective (lam ∘ s.1)) :
    unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom
          ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj))) := by
  classical
  simp only [unitPullback, dif_pos hinj]

theorem unitPullback_apply_of_not_injective (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (z : (unit πY).cochain 𝒦 n) (s : 𝒲.Idx n) (hinj : ¬ Function.Injective (lam ∘ s.1)) :
    unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s = 0 := by
  classical
  simp only [unitPullback, dif_neg hinj]

end AlgebraicGeometry.OModulePresheaf

end
