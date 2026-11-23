module

public import Theorem.Submodule.LocalBox
public import Class.CerednikDrinfeld_MumfordPeriod
public import Abbrev.CerednikDrinfeld_CosetGraphAtPrime

public noncomputable section

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld.CosetGraph

variable {a b : ℚ}


public theorem smul_vert_mk (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) (g : (Loc a b v)ˣ) :
    γ • ((g : (Loc a b v)ˣ) : Vert R v) = ((toLoc v γ * g : (Loc a b v)ˣ) : Vert R v) := rfl


public theorem mk_smul_vert (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : awayUnits R v) (x : Vert R v) :
    (QuotientGroup.mk γ : ProjAwayUnits R v) • x = γ • x := rfl


public theorem coe_smul_vert_mk (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (γ : awayUnits R v)
    (g : (Loc a b v)ˣ) :
    γ • ((g : (Loc a b v)ˣ) : Vert R v) = ((toLoc v (γ : (ℍ[ℚ, a, b])ˣ) * g : (Loc a b v)ˣ) : Vert R v) := rfl

end CerednikDrinfeld.CosetGraph

end
