module

public import Mathlib
public import Def.LinearMap_DatumAndHonda
public import Def.RingHom_WittVectorHom

@[expose] public section

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

noncomputable def verschiebungIter (k : ℕ) : WittVector p R →+ WittVector p R where
  toFun x := (WittVector.verschiebung (p := p) (R := R))^[k] x
  map_zero' := iterate_map_zero _ _
  map_add' := iterate_map_add _ _

noncomputable def shiftLE (h : n ≤ m) :
    TruncatedWittVector p n R →+ TruncatedWittVector p m R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate m).toAddMonoidHom.comp (verschiebungIter (m - n)),
      fun x hx => by
        change (WittVector.truncate n) x = 0 at hx
        rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
        change (WittVector.truncate m) ((WittVector.verschiebung (p := p) (R := R))^[m - n] x) = 0
        ext ⟨i, hi⟩
        simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
        by_cases him : i < m - n
        · exact WittVector.iterate_verschiebung_coeff_eq_zero x him
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + (m - n) := ⟨i - (m - n), by omega⟩
          rw [WittVector.iterate_verschiebung_coeff]
          exact hx k (by omega)⟩

end TruncWitt

section WittHom

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra R A]

open TruncWitt

variable (R p A) in

noncomputable def wittHomShiftLE (h : n ≤ m) : wittHom R p n A →+ wittHom R p m A where
  toFun x := ⟨TruncWitt.shiftLE h x, shiftLE_mem_wittHom h x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

end WittHom

section Colimit

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra R A]

def DieudonneModule : Type v :=
  AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h

namespace DieudonneModule

noncomputable def of (n : ℕ) : wittHom R p n A →+ DieudonneModule R p A :=
  AddCommGroup.DirectLimit.of (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h) n

variable {R p A}
variable {n m : ℕ}

section Lift

variable {P : Type w} [AddCommGroup P]

variable (R p A) in

noncomputable def lift (g : ∀ n, wittHom R p n A →+ P)
    (hg : ∀ (n : ℕ) (x : wittHom R p n A), g (n + 1) (wittHomShift R p n A x) = g n x) :
    DieudonneModule R p A →+ P :=
  AddCommGroup.DirectLimit.lift (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h)
    P g fun _ _ h x => compat_shiftLE g hg h x

end Lift

variable (R p A) in

noncomputable def verschiebung : DieudonneModule R p A →+ DieudonneModule R p A :=
  lift R p A (fun n => (of R p A n).comp (wittHomVerschiebung R p n A)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← wittHomShift_verschiebung, of_shift]

section CharP

variable [CharP R p]

variable (R p A) in

noncomputable def frobenius : DieudonneModule R p A →+ DieudonneModule R p A :=
  lift R p A (fun n => (of R p A n).comp (wittHomFrobenius R p n A)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← wittHomShift_frobenius, of_shift]

variable (R p A) in

noncomputable def dieudonneDatum : DieudonneDatum (p : ℤ) (DieudonneModule R p A) where
  F := (frobenius R p A).toIntLinearMap
  V := (verschiebung R p A).toIntLinearMap
  fv := LinearMap.ext fun z => frobenius_verschiebung z
  vf := LinearMap.ext fun z => verschiebung_frobenius z

end CharP

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

variable (R p) in

noncomputable def map (φ : A →ₐc[R] B) : DieudonneModule R p A →+ DieudonneModule R p B :=
  lift R p A (fun n => (of R p B n).comp (wittHomMap p n φ)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, wittHomMap_shift, of_shift]

end Map

end DieudonneModule

end Colimit

namespace DieudonneModule.Examples

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev Ga : Type u := SymmetricAlgebra R R

noncomputable def coordinate : Ga R := SymmetricAlgebra.ι R R 1

end DieudonneModule.Examples

end Deformation

end
