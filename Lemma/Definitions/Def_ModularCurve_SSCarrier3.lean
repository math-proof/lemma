import Lemma.Definitions.Def_ModularCurve_ModPFormFn

set_option autoImplicit false

noncomputable section

namespace ModularCurve

variable (F : Type) [Field F] (N' : ℕ) [NeZero N']

abbrev ssPlaces3 : Type :=
  {x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') //
    0 < x.ord (ModularCurve.jGeomGen F N')}

abbrev SSCarrier3 : Type := (x : ssPlaces3 F N') → x.1.ResidueField

namespace SSCarrier3

variable {F N'}

def aPole (m : ℕ) (x : ssPlaces3 F N') : ℤ :=
  7 * (m : ℤ) * x.1.ord (ModularCurve.jGeomGen F N') / 6 + 1

def uniformizer (x : ssPlaces3 F N') : ↥(ModularCurve.modularFunctionFieldC F N') :=
  Classical.epsilon fun π : ↥(ModularCurve.modularFunctionFieldC F N') => x.1.ord π = 1

open Classical in

def res (m : ℕ) (φ : PowerSeries F) (x : ssPlaces3 F N') : x.1.ResidueField :=
  if h : ∃ G : ↥(ModularCurve.modularFunctionFieldC F N'),
      (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ then
    if hm : Classical.choose h * uniformizer x ^ (aPole m x).toNat ∈ x.1.toValuationSubring then
      IsLocalRing.residue x.1.toValuationSubring ⟨_, hm⟩
    else 0
  else 0

end SSCarrier3

end ModularCurve

end
