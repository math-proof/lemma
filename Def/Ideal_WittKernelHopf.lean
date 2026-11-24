module
public import Mathlib
public import Def.LinearMap_DatumAndHonda
public import Def.RingHom_WittVectorHom
public import Def.Int_WittHomColimit
public import Def.AlgHom_WittGroupHopf
public import Class.HopfAlgebra_HopfIdealQuotient
public import Instance.Dieudonne_WittKernelHopf
public import Notation.Dieudonne_WittKernelHopf
set_option autoImplicit false
open Function
open scoped TensorProduct


public section

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

omit hp in
end TruncWitt

namespace WittKernel

open WittGroup TruncWitt

variable (k : Type u) [CommRing k] (p : ℕ) (n a b : ℕ) (J : Type v)

noncomputable def relation (j : J) (i : Fin n) : WittGroup.Coord k p n J :=
  X j i ^ p ^ b - X j i ^ p ^ a

noncomputable def ideal : Ideal (WittGroup.Coord k p n J) :=
  Ideal.span (Set.range fun ji : J × Fin n => relation k p n a b J ji.1 ji.2)

variable {k p n a b J}

variable [hp : Fact p.Prime]

section HopfIdeal

variable [CharP k p]

variable (k p n a b J)

open scoped Dieudonne_WittKernelHopf

omit [CharP k p] in

end HopfIdeal

variable (k p n a b J)

abbrev Coord : Type (max u v) := WittGroup.Coord k p n J ⧸ ideal k p n a b J

variable [CharP k p]

noncomputable def π : WittGroup.Coord k p n J →ₐc[k] Coord k p n a b J :=
  HopfAlgebra.quotientBialgHom k (ideal k p n a b J)

variable {k p n a b J}

variable (k p n a b J)

noncomputable def tauto (j : J) : wittHom k p n (Coord k p n a b J) :=
  wittHomMap p n (π k p n a b J) (univHom j)

variable {k p n a b J}

variable (k p n a b J) in

noncomputable def tautoClass (j : J) : DieudonneModule k p (Coord k p n a b J) :=
  DieudonneModule.of k p (Coord k p n a b J) n (tauto k p n a b J j)

section Points

variable {T : Type w} [CommRing T] [Algebra k T]

noncomputable def pointsEquiv :
    (Coord k p n a b J →ₐ[k] T) ≃
      {x : J → TruncatedWittVector p n T // ∀ j, frobeniusFun^[b] (x j) = frobeniusFun^[a] (x j)} where
  toFun f := ⟨WittGroup.pointsEquiv (f.comp (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] _)),
    fun j => by
      have hle : ideal k p n a b J ≤ RingHom.ker
          (f.comp (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] _)).toRingHom := by
        intro x hx
        rw [RingHom.mem_ker]
        change f (π k p n a b J x) = 0
        rw [π_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
      have := (ideal_le_ker_iff _).1 hle j
      rwa [← pointsEquiv_eq_map_univ] at this⟩
  invFun x := Ideal.Quotient.liftₐ (ideal k p n a b J) (WittGroup.pointsEquiv.symm x.1)
    (fun y hy => (ideal_le_ker_iff (WittGroup.pointsEquiv.symm x.1 :
        WittGroup.Coord k p n J →ₐ[k] T).toRingHom).2 (fun j => by
      rw [← pointsEquiv_eq_map_univ, Equiv.apply_symm_apply]
      exact x.2 j) hy)
  left_inv f := by
    refine Ideal.Quotient.algHom_ext k ?_
    rw [Ideal.Quotient.liftₐ_comp, Equiv.symm_apply_apply]
    rfl
  right_inv x := by
    apply Subtype.ext
    change WittGroup.pointsEquiv _ = x.1
    conv_rhs => rw [← (WittGroup.pointsEquiv (R := k) (p := p) (n := n) (J := J)).apply_symm_apply x.1]
    congr 1

end Points

end WittKernel

end Deformation
