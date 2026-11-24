module
public import Mathlib
public import Def.GaloisRep_Flat
public import Def.FLTPrelim_Ramification
public import Instance.GaloisRep_InertiaRing
public import Abbrev.GaloisRep_InertiaRing
public import Notation.GaloisRep_InertiaRing
set_option autoImplicit false


public section

noncomputable section

namespace GaloisRep

open scoped GaloisRep_InertiaRing

def inertiaRing (A : ValuationSubring ℚ̄) : Subring ℚ̄ := A.toSubring ⊓ (inertiaField A).toSubring

namespace InertiaRing

variable (A : ValuationSubring ℚ̄)

variable {A} in

def mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x) : inertiaRing A :=
  ⟨x, GaloisRep.mem_inertiaRing_iff.mpr ⟨hxA, GaloisRep.mem_inertiaField_iff.mpr hfix⟩⟩

end InertiaRing

end GaloisRep

end

section PointTransportSection

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
open WithConv

namespace GaloisRep.PointTransport

section LiftPt

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Algebra R H]

noncomputable def liftPt (φ : WithConv (H →ₐ[R] L)) : WithConv (S ⊗[R] H →ₐ[S] L) :=
  toConv (Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv fun _ _ => .all _ _)

end LiftPt

section LiftPtConv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

end LiftPtConv

section EvGen

variable (K : Type*) (L : Type*) (B : Type*) [CommRing K] [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]

noncomputable def evGen : L ⊗[K] B →ₐ[L] (WithConv (B →ₐ[K] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (Pi.algHom K _ fun ν : WithConv (B →ₐ[K] L) => (WithConv.ofConv ν : B →ₐ[K] L)) (fun _ _ => Commute.all _ _)

variable {K L B}
variable {S : Type*} [CommRing S] [Algebra K S] [Algebra S L] [IsScalarTower K S L]

noncomputable def liftPtEquiv : WithConv (B →ₐ[K] L) ≃ WithConv (S ⊗[K] B →ₐ[S] L) :=
  Equiv.ofBijective (liftPt (S := S)) ⟨liftPt_injective, liftPt_surjective⟩

end EvGen

section LiftPtMulEquiv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

noncomputable def liftPtMulEquiv : WithConv (H →ₐ[R] L) ≃* WithConv (S ⊗[R] H →ₐ[S] L) :=
  { liftPtEquiv (K := R) (L := L) (B := H) (S := S) with map_mul' := liftPt_mul }

end LiftPtMulEquiv

section Valuative

variable {R S L H : Type*} [CommRing R] [CommRing S] [Field L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

end Valuative

end GaloisRep.PointTransport

noncomputable section

namespace AlgHom.InertiaRing

section Dec

open scoped GaloisRep_InertiaRing

variable (A : ValuationSubring ℚ̄)

noncomputable def galF {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : ℚ̄ ≃ₐ[GaloisRep.inertiaField A] ℚ̄ :=
  { σ with commutes' := fun x => GaloisRep.mem_inertiaField_iff.mp x.2 σ hσ }

noncomputable def rhoI (σ : A.inertiaSubgroupIn ℚ) : ℚ̄ ≃ₐ[GaloisRep.inertiaField A] ℚ̄ := galF A σ.2

noncomputable def galO {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : ℚ̄ →ₐ[GaloisRep.inertiaRing A] ℚ̄ :=
  { (σ : ℚ̄ →+* ℚ̄) with commutes' := fun z => AlgHom.InertiaRing.coe_fixed A z σ hσ }

variable (q : ℕ) [Fact q.Prime]

@[reducible] noncomputable def algebraRO (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) :
    Algebra (GaloisRep.ratLocalizedAt q) (GaloisRep.inertiaRing A) :=
  RingHom.toAlgebra
    { toFun := fun r => GaloisRep.InertiaRing.mkO (((r : ℚ) : ℚ̄)) (ratCast_mem_of_coprime A q hA r.2)
        (fun σ _ => by rw [← eq_ratCast (algebraMap ℚ ℚ̄), AlgEquiv.commutes])
      map_one' := Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_one]; push_cast; try rfl)
      map_mul' := fun a b => Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_mul]; push_cast; try rfl)
      map_zero' := Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_zero]; push_cast; try rfl)
      map_add' := fun a b => Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_add]; push_cast; try rfl) }

end Dec

section T1

open scoped GaloisRep_InertiaRing

variable (A : ValuationSubring ℚ̄)
variable {S : Type*} [CommRing S] [Bialgebra (GaloisRep.inertiaRing A) S] [Module.Finite (GaloisRep.inertiaRing A) S]

noncomputable def toQbarPt (x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) :
    WithConv (S →ₐ[GaloisRep.inertiaRing A] ℚ̄) :=
  toConv ((Algebra.ofId (GaloisRep.inertiaRing A) ℚ̄).comp x.ofConv)

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
end T1

end AlgHom.InertiaRing

end

end PointTransportSection
