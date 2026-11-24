module
public import Mathlib
public import Def.LinearMap_DatumAndHonda
public import Def.RingHom_WittVectorHom
public import Instance.Dieudonne_WittGroupHopf
public import Notation.Dieudonne_WittGroupHopf
set_option autoImplicit false
open Function
open scoped TensorProduct


public section

universe u v w

namespace Deformation

set_option linter.unusedVariables false in

def WittGroup.Coord (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v) : Type (max u v) :=
  MvPolynomial (J × Fin n) R

namespace WittGroup

variable (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v)

variable {R p n J}

noncomputable def X (j : J) (i : Fin n) : Coord R p n J := (MvPolynomial.X (j, i) : MvPolynomial (J × Fin n) R)

noncomputable def lift {A : Type w} [CommSemiring A] [Algebra R A] (f : J → Fin n → A) :
    Coord R p n J →ₐ[R] A :=
  (MvPolynomial.aeval fun ji : J × Fin n => f ji.1 ji.2 : MvPolynomial (J × Fin n) R →ₐ[R] A)

variable (R p n) in

noncomputable def univ (j : J) : TruncatedWittVector p n (Coord R p n J) :=
  TruncatedWittVector.mk p fun i => X j i

variable [hp : Fact p.Prime]


section Rehom

variable {S : Type*} {B : Type*} [NonAssocSemiring S] [NonAssocSemiring B]

omit hp in

def rehom (g : S → B) (h1 : g 1 = 1) (hm : ∀ x y, g (x * y) = g x * g y) (h0 : g 0 = 0)
    (ha : ∀ x y, g (x + y) = g x + g y) : S →+* B :=
  ⟨⟨⟨g, h1⟩, hm⟩, h0, ha⟩

omit hp in
end Rehom

variable (R p n J)

noncomputable def univLeft (j : J) : TruncatedWittVector p n (Coord R p n J ⊗[R] Coord R p n J) :=
  TruncatedWittVector.mk p fun i => X j i ⊗ₜ[R] (1 : Coord R p n J)

noncomputable def univRight (j : J) : TruncatedWittVector p n (Coord R p n J ⊗[R] Coord R p n J) :=
  TruncatedWittVector.mk p fun i => (1 : Coord R p n J) ⊗ₜ[R] X j i

noncomputable def comul : Coord R p n J →ₐ[R] Coord R p n J ⊗[R] Coord R p n J :=
  lift fun j i => (univLeft R p n J j + univRight R p n J j).coeff i

noncomputable def counit : Coord R p n J →ₐ[R] R :=
  lift fun _ _ => 0

noncomputable def antipode : Coord R p n J →ₐ[R] Coord R p n J :=
  lift fun j i => (-univ R p n j).coeff i

variable {R p n J}


variable (R p n J)

variable {R p n J}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

noncomputable def pointsEquiv : (Coord R p n J →ₐ[R] A) ≃ (J → TruncatedWittVector p n A) where
  toFun φ j := TruncatedWittVector.mk p fun i => φ (X j i)
  invFun x := lift fun j i => (x j).coeff i
  left_inv φ := algHom_ext fun j i => by rw [lift_X, TruncatedWittVector.coeff_mk]
  right_inv x := funext fun j => TruncatedWittVector.ext fun i => by
    rw [TruncatedWittVector.coeff_mk, lift_X]

omit hp in
end Points

noncomputable def univHom (j : J) : wittHom R p n (Coord R p n J) := ⟨univ R p n j, univ_mem_wittHom j⟩

end WittGroup

end Deformation
