module

public import Mathlib
public import Def.NumberField_SelmerRepModP
public import Theorem.Rep.LevelArithmeticModP
public import Instance.NumberField_SelmerRepModP

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped NumberField NumberField.LevelArith Pointwise Rep

namespace NumberField.LevelArith

section Selmer

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ)

omit [NumberField E] [NumberField F] in
def selmer : Subgroup (unitsModPow F p) :=
  (selmerGroup (R := 𝓞 F) (K := F) (S := NumberField.SUnits.placesAbove E F S) (n := p) : Subgroup (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range))

omit [NumberField E] in
def selmerStable : Subgroup (unitsModPow F p) :=
  ⨅ σ : F ≃ₐ[E] F, (selmer E F S p).comap (MulDistribMulAction.toMonoidHom (unitsModPow F p) σ)

omit [NumberField E] in
def selmerSubmodule : Submodule ℤ (Additive (unitsModPow F p)) := (Subgroup.toAddSubgroup (selmerStable E F S p)).toIntSubmodule

omit [NumberField E] in
abbrev selmerRepInt : Rep ℤ (F ≃ₐ[E] F) :=
  Rep.of ((Representation.ofMulDistribMulAction (F ≃ₐ[E] F) (unitsModPow F p)).subrepresentation (selmerSubmodule E F S p)
    fun σ x hx => by
      have hx' : Additive.toMul x ∈ selmerStable E F S p := (mem_selmerSubmodule E F S p x).1 hx
      have hρ := Representation.ofMulDistribMulAction_apply_apply
        (M := F ≃ₐ[E] F) (G := unitsModPow F p) σ x
      have : Additive.toMul
          (Representation.ofMulDistribMulAction (F ≃ₐ[E] F) (unitsModPow F p) σ x)
          ∈ selmerStable E F S p := by
        rw [hρ, toMul_ofMul]
        exact smul_mem_selmerStable E F S p σ hx'
      exact (mem_selmerSubmodule E F S p _).2 this)

omit [NumberField E] in
@[reducible] noncomputable def selmerRepIntZModModule : Module (ZMod p) ↑(selmerRepInt E F S p) :=
  AddCommGroup.zmodModule (nsmul_selmer_eq_zero E F S p)

omit [NumberField E] in

abbrev selmerRepField : Rep (ZMod p) (F ≃ₐ[E] F) :=
  letI := selmerRepIntZModModule E F S p
  Rep.of (toZMod p (selmerRepInt E F S p).ρ)

omit [NumberField E] in

def fromSUnitsLinear : NumberField.SUnits.sUnitsRep E F S →ₗ[ℤ] selmerRepInt E F S p where
  toFun u := ⟨Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u)), mk_mem_selmerStable E F S p u⟩
  map_add' _ _ := rfl
  map_smul' n u := Subtype.ext (by
    change Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S (n • u))) =
      n • Additive.ofMul (unitsModPow.mk F p (NumberField.SUnits.val E F S u))
    rw [NumberField.SUnits.val_zsmul]
    exact (QuotientGroup.mk_zpow ((powMonoidHom p : Fˣ →* Fˣ).range) (NumberField.SUnits.val E F S u) n :))

def fromSUnitsModP : repModP p (NumberField.SUnits.sUnitsRep E F S) ⟶ selmerRepField E F S p :=
  letI := selmerRepIntZModModule E F S p
  Rep.ofHom ⟨(Submodule.liftQ _ (fromSUnitsLinear E F S p) (smul_top_le_ker p _ (nsmul_selmer_eq_zero E F S p))).toAddMonoidHom.toZModLinearMap p,
    fun σ => LinearMap.ext fun x => by
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl⟩

omit [NumberField E] in
end Selmer

section Level

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (S : Finset Nat.Primes) (p : ℕ)

abbrev selmerRep : Rep (ZMod p) ↥K.fixingSubgroup :=
  inflLevel K L hKL (selmerRepField ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p)

abbrev unitsModPToSelmerRep : unitsModP K L hKL S p ⟶ selmerRep K L hKL S p :=
  (Rep.resFunctor (levelGal K L hKL)).map (fromSUnitsModP ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p)

end Level

end NumberField.LevelArith

end
