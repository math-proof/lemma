module

public import Mathlib
public import Def.AlgebraicCurve_RegularDifferentials
public import Theorem.Scheme.CanonicalDivisorUniformizer
public import Def.AlgebraicCurve_GluedPic0

@[expose] public section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

def IsRegularAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord

def HasSimplePoleAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f : F, v.uniformizer * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord

def HasSimpleResidue (ω : Ω[F⁄K]) (a : K) : Prop :=
  ∃ f : F, ω = f • v.dCoord ∧ v.HasValue (v.uniformizer * f) a

variable {v}


end Place

section Polar

variable (K F)

def polarDifferentials (S : Set (Place K F)) : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, (v ∉ S → v.IsRegularAt ω) ∧ (v ∈ S → v.HasSimplePoleAt ω)}
  zero_mem' v := ⟨fun _ => v.isRegularAt_zero, fun _ => v.hasSimplePoleAt_zero⟩
  add_mem' hω hη v :=
    ⟨fun hv => ((hω v).1 hv).add ((hη v).1 hv), fun hv => ((hω v).2 hv).add ((hη v).2 hv)⟩
  smul_mem' c _ hω v := ⟨fun hv => ((hω v).1 hv).smul c, fun hv => ((hω v).2 hv).smul c⟩

variable {K F}

end Polar

section Glued

variable (K F)

def IsGluedPolarPair (S : Set (Place K F × Place K F)) (ω : Ω[F⁄K] × Ω[F⁄K]) : Prop :=
  ω.1 ∈ polarDifferentials K F (Prod.fst '' S) ∧ ω.2 ∈ polarDifferentials K F (Prod.snd '' S) ∧
    ∀ s ∈ S, ∀ a b : K, s.1.HasSimpleResidue ω.1 a → s.2.HasSimpleResidue ω.2 b → a + b = 0

def gluedPolarDifferentials (S : Set (Place K F × Place K F)) : Submodule K (Ω[F⁄K] × Ω[F⁄K]) :=
  Submodule.span K {ω | IsGluedPolarPair K F S ω}

variable {K F}

variable (K F) in

def gluedPolarDifferentials.fst (S : Set (Place K F × Place K F)) :
    gluedPolarDifferentials K F S →ₗ[K] polarDifferentials K F (Prod.fst '' S) :=
  ((LinearMap.fst K Ω[F⁄K] Ω[F⁄K]).domRestrict _).codRestrict _ fun ω =>
    (gluedPolarDifferentials_le_prod S ω.2).1

variable (K F) in

def gluedPolarDifferentials.snd (S : Set (Place K F × Place K F)) :
    gluedPolarDifferentials K F S →ₗ[K] polarDifferentials K F (Prod.snd '' S) :=
  ((LinearMap.snd K Ω[F⁄K] Ω[F⁄K]).domRestrict _).codRestrict _ fun ω =>
    (gluedPolarDifferentials_le_prod S ω.2).2

end Glued

end AlgebraicCurve

end

end
