module

public import Mathlib
public import Instance.AlgebraicGeometry_ProjSpaceCechTwist
public import Abbrev.AlgebraicGeometry_ProjSpaceCechTwist

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open Finset Function

namespace ProjSpaceCech

public theorem Idx.succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i
      = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  ext k
  simp only [Function.comp_apply, Fin.succAbove]
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at H
  simp only [Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc] <;> omega

section Setup

variable (n : ℕ)


public theorem Twist.mem_negSupp {a : Twist.MonExp n} {j : Fin (n + 1)} :
    j ∈ Twist.negSupp n a ↔ a j < 0 := by
  simp [Twist.negSupp]


public theorem Twist.Mon.incl_injective (d : ℤ) {I J : Finset (Fin (n + 1))}
    (hIJ : I ⊆ J) : Function.Injective (Twist.Mon.incl n d hIJ) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  exact Subtype.ext (Subtype.mk.inj h)


public theorem Twist.Mon.incl_val (d : ℤ) {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (a : Twist.Mon n d I) :
    (Twist.Mon.incl n d hIJ a).1 = a.1 := rfl


public theorem Idx.card_img {i : ℕ} (s : Idx n i) :
    (Idx.img n s).card = i + 1 := by
  rw [Idx.img, Finset.card_image_of_injective _ s.2.injective,
    Finset.card_univ, Fintype.card_fin]


public theorem Idx.img_face_subset {i : ℕ} (s : Idx n (i + 1))
    (j : Fin (i + 2)) :
    Idx.img n (Idx.face n s j) ⊆ Idx.img n s := by
  intro x hx
  simp only [Idx.img, Idx.face, mem_image, mem_univ, true_and] at *
  obtain ⟨k, hk⟩ := hx
  exact ⟨Fin.succAbove j k, hk⟩


public theorem Twist.d_apply (i : ℕ) (f : Twist.cochain R n d i)
    (s : Idx n (i + 1)) :
    Twist.d R n d i f s =
      ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Twist.faceRes R n d s j (f (Idx.face n s j)) := by
  simp only [Twist.d, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]


public theorem Idx.isEmpty_of_lt {i : ℕ} (hi : n < i) :
    IsEmpty (Idx n i) := by
  rw [Idx, isEmpty_subtype]
  intro s hs
  have := Fintype.card_le_of_injective s hs.injective
  simp only [Fintype.card_fin] at this; omega


public theorem Twist.cochain_subsingleton_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.cochain R n d i) := by
  have := Idx.isEmpty_of_lt n hi
  exact ⟨fun f g => funext fun s => (this.false s).elim⟩

end AltCech

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

