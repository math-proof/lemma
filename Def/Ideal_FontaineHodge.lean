module

public import Mathlib
public import Def.LinearMap_DatumAndHonda
public import Def.RingHom_WittVectorHom
public import Def.Int_WittHomColimit
public import Abbrev.Dieudonne_FontaineHodge

@[expose] public section

set_option autoImplicit false

open Function

universe u v w u'

namespace Deformation


namespace TruncWitt

section FontaineKer

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] (π : ℛ →+* A)

noncomputable def fontaineKer : AddSubgroup (TruncatedWittVector p n A) where
  carrier := {a | ∃ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a ∧
    WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n}}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨X, rfl, hX⟩ ⟨Y, rfl, hY⟩
    exact ⟨X + Y, by simp, by rw [map_add]; exact add_mem hX hY⟩
  neg_mem' := by
    rintro a ⟨X, rfl, hX⟩
    exact ⟨-X, by simp, by rw [map_neg]; exact neg_mem hX⟩

variable {p n π}


end FontaineKer

end TruncWitt

section Hodge

variable (R : Type w) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] [Bialgebra R A] (π : ℛ →+* A)

open TruncWitt DieudonneModule

noncomputable def fontaineHodgeLevel : AddSubgroup (wittHom R p n A) :=
  (fontaineKer p n π).addSubgroupOf (wittHom R p n A)

variable {R p n π}

variable (R p π) in

noncomputable def fontaineHodgeAddSubgroup : AddSubgroup (DieudonneModule R p A) where
  carrier := {z | ∃ (n : ℕ) (x : wittHom R p n A),
    (x : TruncatedWittVector p n A) ∈ fontaineKer p n π ∧ DieudonneModule.of R p A n x = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, x, hx, rfl⟩ ⟨m, y, hy, rfl⟩
    refine ⟨max n m, wittHomShiftLE R p A (le_max_left n m) x +
      wittHomShiftLE R p A (le_max_right n m) y, ?_, ?_⟩
    · exact add_mem (shiftLE_mem_fontaineKer _ hx) (shiftLE_mem_fontaineKer _ hy)
    · rw [map_add, of_shiftLE, of_shiftLE]
  neg_mem' := by
    rintro _ ⟨n, x, hx, rfl⟩
    exact ⟨n, -x, neg_mem hx, map_neg _ _⟩

variable (R p π) in

noncomputable def fontaineHodge : Submodule ℤ (DieudonneModule R p A) :=
  (fontaineHodgeAddSubgroup R p π).toIntSubmodule

end Hodge


end Deformation
