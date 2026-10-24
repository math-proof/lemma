import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open Finset Function

namespace ProjSpaceCech

theorem Idx.succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
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

abbrev Twist.MonExp := Fin (n + 1) → ℤ

def Twist.negSupp (a : Twist.MonExp n) : Finset (Fin (n + 1)) :=
  univ.filter (fun j => a j < 0)

theorem Twist.mem_negSupp {a : Twist.MonExp n} {j : Fin (n + 1)} :
    j ∈ Twist.negSupp n a ↔ a j < 0 := by
  simp [Twist.negSupp]

def Twist.Mon (d : ℤ) (I : Finset (Fin (n + 1))) : Type :=
  {a : Twist.MonExp n // ∑ j, a j = d ∧ Twist.negSupp n a ⊆ I}

instance Twist.Mon.instDecidableEq (d : ℤ) (I : Finset (Fin (n + 1))) :
    DecidableEq (Twist.Mon n d I) := Classical.decEq _

def Twist.Mon.incl (d : ℤ) {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    Twist.Mon n d I → Twist.Mon n d J :=
  fun a => ⟨a.1, a.2.1, a.2.2.trans hIJ⟩

theorem Twist.Mon.incl_injective (d : ℤ) {I J : Finset (Fin (n + 1))}
    (hIJ : I ⊆ J) : Function.Injective (Twist.Mon.incl n d hIJ) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  exact Subtype.ext (Subtype.mk.inj h)

theorem Twist.Mon.incl_val (d : ℤ) {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (a : Twist.Mon n d I) :
    (Twist.Mon.incl n d hIJ a).1 = a.1 := rfl

abbrev Twist.Sec (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (I : Finset (Fin (n + 1))) : Type u :=
  Twist.Mon n d I →₀ R

end Setup

section AltCech

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

def Idx (i : ℕ) : Type := {s : Fin (i + 1) → Fin (n + 1) // StrictMono s}

instance Idx.instFintype (i : ℕ) : Fintype (Idx n i) := Subtype.fintype _

instance Idx.instDecidableEq (i : ℕ) : DecidableEq (Idx n i) := Classical.decEq _

def Idx.img {i : ℕ} (s : Idx n i) : Finset (Fin (n + 1)) :=
  Finset.univ.image s.1

theorem Idx.card_img {i : ℕ} (s : Idx n i) :
    (Idx.img n s).card = i + 1 := by
  rw [Idx.img, Finset.card_image_of_injective _ s.2.injective,
    Finset.card_univ, Fintype.card_fin]

def Idx.face {i : ℕ} (s : Idx n (i + 1)) (j : Fin (i + 2)) :
    Idx n i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem Idx.img_face_subset {i : ℕ} (s : Idx n (i + 1))
    (j : Fin (i + 2)) :
    Idx.img n (Idx.face n s j) ⊆ Idx.img n s := by
  intro x hx
  simp only [Idx.img, Idx.face, mem_image, mem_univ, true_and] at *
  obtain ⟨k, hk⟩ := hx
  exact ⟨Fin.succAbove j k, hk⟩

def Twist.faceRes {i : ℕ} (s : Idx n (i + 1)) (j : Fin (i + 2)) :
    Twist.Sec R n d (Idx.img n (Idx.face n s j))
      →ₗ[R] Twist.Sec R n d (Idx.img n s) :=
  Finsupp.lmapDomain R R (Twist.Mon.incl n d (Idx.img_face_subset n s j))

abbrev Twist.cochain (i : ℕ) : Type u :=
  ∀ s : Idx n i, Twist.Sec R n d (Idx.img n s)

instance Twist.cochain.instAddCommGroup (i : ℕ) : AddCommGroup (Twist.cochain R n d i) :=
  inferInstanceAs (AddCommGroup (∀ s, _ →₀ R))

instance Twist.cochain.instModule (i : ℕ) : Module R (Twist.cochain R n d i) :=
  inferInstanceAs (Module R (∀ s, _ →₀ R))

end AltCech

def Twist.d (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    Twist.cochain R n d i →ₗ[R] Twist.cochain R n d (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Twist.faceRes R n d s j).comp (LinearMap.proj (Idx.face n s j)))

section AltCech

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

theorem Twist.d_apply (i : ℕ) (f : Twist.cochain R n d i)
    (s : Idx n (i + 1)) :
    Twist.d R n d i f s =
      ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Twist.faceRes R n d s j (f (Idx.face n s j)) := by
  simp only [Twist.d, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem Idx.isEmpty_of_lt {i : ℕ} (hi : n < i) :
    IsEmpty (Idx n i) := by
  rw [Idx, isEmpty_subtype]
  intro s hs
  have := Fintype.card_le_of_injective s hs.injective
  simp only [Fintype.card_fin] at this; omega

theorem Twist.cochain_subsingleton_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.cochain R n d i) := by
  have := Idx.isEmpty_of_lt n hi
  exact ⟨fun f g => funext fun s => (this.false s).elim⟩

end AltCech

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

def Twist.H : ℕ → Type u
  | 0 => LinearMap.ker (Twist.d R n d 0)
  | (i + 1) =>
      LinearMap.ker (Twist.d R n d (i + 1)) ⧸
        (LinearMap.range (Twist.d R n d i)).comap
          (LinearMap.ker (Twist.d R n d (i + 1))).subtype

instance Twist.H.addCommGroup (i : ℕ) : AddCommGroup (Twist.H R n d i) :=
  match i with
  | 0 => inferInstanceAs (AddCommGroup
      ↥(LinearMap.ker (Twist.d R n d 0)))
  | (j + 1) => inferInstanceAs (AddCommGroup
      (↥(LinearMap.ker (Twist.d R n d (j + 1))) ⧸ _))

instance Twist.H.module (i : ℕ) : Module R (Twist.H R n d i) :=
  match i with
  | 0 => inferInstanceAs (Module R
      ↥(LinearMap.ker (Twist.d R n d 0)))
  | (j + 1) => inferInstanceAs (Module R
      (↥(LinearMap.ker (Twist.d R n d (j + 1))) ⧸ _))

end Cohomology

end ProjSpaceCech

end
