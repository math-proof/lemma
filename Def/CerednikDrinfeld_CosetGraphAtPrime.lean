module

public import Theorem.Submodule.LocalBox
public import Class.CerednikDrinfeld_MumfordPeriod
public import Abbrev.CerednikDrinfeld_CosetGraphAtPrime

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld.CosetGraph

variable {a b : ℚ}

def toLoc (v : HeightOneSpectrum (𝓞 ℚ)) : (ℍ[ℚ, a, b])ˣ →* (Loc a b v)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : ℍ[ℚ, a, b] →ₐ[ℚ] Loc a b v).toRingHom.toMonoidHom

def scalarUnits (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (Loc a b v)ˣ :=
  (Units.map (Algebra.TensorProduct.includeRight : v.adicCompletion ℚ →ₐ[ℚ] Loc a b v).toRingHom.toMonoidHom).range

def level (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (Loc a b v)ˣ :=
  Subgroup.closure (Submodule.localBoxUnits R v) ⊔ scalarUnits v

abbrev Vert (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Type := (Loc a b v)ˣ ⧸ level R v

def graph (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (nv : (Loc a b v)ˣ) : SimpleGraph (Vert R v) where
  Adj x y := x ≠ y ∧ ∃ g : (Loc a b v)ˣ, ∃ k ∈ level R v,
    (x = (g : Vert R v) ∧ y = ((g * k * nv : (Loc a b v)ˣ) : Vert R v)) ∨
      (y = (g : Vert R v) ∧ x = ((g * k * nv : (Loc a b v)ˣ) : Vert R v))
  symm := ⟨by
    rintro x y ⟨hne, g, k, hk, h⟩
    exact ⟨hne.symm, g, k, hk, h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def awayUnits (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (ℍ[ℚ, a, b])ˣ :=
  ⨅ (w : HeightOneSpectrum (𝓞 ℚ)) (_ : w ≠ v), (Subgroup.closure (Submodule.localBoxUnits R w)).comap (toLoc w)

def actionKer (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (awayUnits R v) :=
  (MulAction.toPermHom (awayUnits R v) (Vert R v)).ker

abbrev ProjAwayUnits (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Type :=
  (awayUnits R v) ⧸ actionKer R v

end CerednikDrinfeld.CosetGraph

end

end
