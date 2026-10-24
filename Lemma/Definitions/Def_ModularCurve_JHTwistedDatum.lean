import Lemma.Definitions.Def_ModularCurve_JHTwistType

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

structure TwistedFibreDatum {p M : ℕ} {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} {A : ValuationSubring (AlgebraicClosure ℚ)}
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) where

  unifFst : ↥SS → Fbar p M H hpM (ResidueField ↥A)

  unifSnd : ↥SS → Fbar p M H hpM (ResidueField ↥A)

  corrFst : ↥SS → Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))

  corrSnd : ↥SS → Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))

  u0 : ↥SS → (ResidueField ↥A)ˣ
  lam : ↥SS → (ResidueField ↥A)ˣ
  mu : ↥SS → (ResidueField ↥A)ˣ

section
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
variable (Psp : JHPlaceSpecialization p M H hpM A)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
  (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (e : ↥SS → ℕ) (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
  (dat : TwistedFibreDatum (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS)

open Classical in

def twistAnnulusDeg (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  ∑ V ∈ D.support with V ∈ (An s).dom, D V

open Classical in

def twistPosMoment (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℚ :=
  ∑ V ∈ D.support with V ∈ (An s).dom, (D V : ℚ) * pos s V

def flipParam (s : ↥SS) : ↥(xHFunctionFieldBar M H) :=
  algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) * ((An s).param)⁻¹

open Classical in

def twistAngFactor (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : (ResidueField ↥A)ˣ :=
  if h : (twistPosMoment SS An pos D s).den = 1 ∧
      ∃ hmem : (∏ V ∈ D.support with V ∈ (An s).dom, (V.evalAt (flipParam SS An s)) ^ (-(D V))) *
          ((p : ℕ) : AlgebraicClosure ℚ) ^ (twistPosMoment SS An pos D s).num ∈ A,
        IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0
  then Units.mk0 (IsLocalRing.residue (R := ↥A) ⟨_, h.2.choose⟩) h.2.choose_spec else 1

open Classical in

def twistCrossFst (s' s : ↥SS) : (ResidueField ↥A)ˣ :=
  if h : (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1.evalAt (dat.unifFst s') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def twistCrossSnd (s' s : ↥SS) : (ResidueField ↥A)ˣ :=
  if h : (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2.evalAt (dat.unifSnd s') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def twistNodeUnit (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : ↥SS → Additive (ResidueField ↥A)ˣ := fun s =>
  Additive.ofMul <|
    (-1 : (ResidueField ↥A)ˣ) ^ (twistAnnulusDeg SS An D s) *
    dat.u0 s ^ (twistEndOrderSnd SS e An pos a D s) *
    dat.lam s ^ (twistEndOrderFst SS e An pos a D s) *
    (dat.mu s ^ (twistEndOrderSnd SS e An pos a D s))⁻¹ *
    twistAngFactor SS An pos D s *
    (∏ s' ∈ Finset.univ.erase s,
      (twistCrossFst SS dat s' s ^ (twistEndOrderFst SS e An pos a D s'))⁻¹ * twistCrossSnd SS dat s' s ^ (twistEndOrderSnd SS e An pos a D s'))

def twistFstSlot (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderFst SS e An pos a D s • dat.corrFst s

def twistSndSlot (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderSnd SS e An pos a D s • dat.corrSnd s

def twistSpData (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS :=
  (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderFst SS e An pos a D s • dat.corrFst s,
    Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderSnd SS e An pos a D s • dat.corrSnd s,
    twistNodeUnit SS e An pos dat a D)

open Classical in

def twistSp (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS :=
  if h : twistSpData Psp α β hα hβ δ SS e An pos dat a D ∈ GluingData.admissible SS then GluedPic0.mk SS ⟨_, h⟩ else 0

end

end JHPlaceSpecialization
end ModularCurve

end
