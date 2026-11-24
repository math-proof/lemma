module
public import Mathlib
public import Instance.AlgebraicGeometry_ProjSpaceCechTwist
public import Abbrev.AlgebraicGeometry_ProjSpaceCechTwist
set_option autoImplicit false


public section

noncomputable section

universe u

open Finset Function

namespace ProjSpaceCech

section Setup

variable (n : ℕ)

def Twist.negSupp (a : Twist.MonExp n) : Finset (Fin (n + 1)) :=
  univ.filter (fun j => a j < 0)

def Twist.Mon (d : ℤ) (I : Finset (Fin (n + 1))) : Type :=
  {a : Twist.MonExp n // ∑ j, a j = d ∧ Twist.negSupp n a ⊆ I}

def Twist.Mon.incl (d : ℤ) {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    Twist.Mon n d I → Twist.Mon n d J :=
  fun a => ⟨a.1, a.2.1, a.2.2.trans hIJ⟩

abbrev Twist.Sec (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (I : Finset (Fin (n + 1))) : Type u :=
  Twist.Mon n d I →₀ R

end Setup

section AltCech

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

def Idx (i : ℕ) : Type := {s : Fin (i + 1) → Fin (n + 1) // StrictMono s}

def Idx.img {i : ℕ} (s : Idx n i) : Finset (Fin (n + 1)) :=
  Finset.univ.image s.1

def Idx.face {i : ℕ} (s : Idx n (i + 1)) (j : Fin (i + 2)) :
    Idx n i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

def Twist.faceRes {i : ℕ} (s : Idx n (i + 1)) (j : Fin (i + 2)) :
    Twist.Sec R n d (Idx.img n (Idx.face n s j))
      →ₗ[R] Twist.Sec R n d (Idx.img n s) :=
  Finsupp.lmapDomain R R (Twist.Mon.incl n d (Idx.img_face_subset n s j))

abbrev Twist.cochain (i : ℕ) : Type u :=
  ∀ s : Idx n i, Twist.Sec R n d (Idx.img n s)

end AltCech

def Twist.d (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    Twist.cochain R n d i →ₗ[R] Twist.cochain R n d (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Twist.faceRes R n d s j).comp (LinearMap.proj (Idx.face n s j)))


section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

def Twist.H : ℕ → Type u
  | 0 => LinearMap.ker (Twist.d R n d 0)
  | (i + 1) =>
      LinearMap.ker (Twist.d R n d (i + 1)) ⧸
        (LinearMap.range (Twist.d R n d i)).comap
          (LinearMap.ker (Twist.d R n d (i + 1))).subtype

end Cohomology

end ProjSpaceCech

end
