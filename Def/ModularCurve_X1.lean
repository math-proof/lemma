module

public import Mathlib
public import Theorem.LaurentSeries.ArithmeticGalois

@[expose] public section

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Restrict

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def restrictForm (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

end Restrict

section Integral

def IsIntegralQExp (f : ℍ → ℂ) (p : PowerSeries ℤ) : Prop :=
  p.map (Int.castRingHom ℂ) = qExpansion 1 f

end Integral

section FunctionField

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ))

def intSeriesC (p : PowerSeries ℤ) : LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K))

def intFormRatiosC : Set (LaurentSeries K) :=
  {x | ∃ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
      IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC K pg ≠ 0 ∧
        x = intSeriesC K pf / intSeriesC K pg}

variable {K Γ} in
def qExpFunctionFieldC : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (intFormRatiosC K Γ)


end FunctionField

section LevelOne

variable (K : Type*) [Field K] (M : ℕ)

def x1FunctionFieldC : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (Gamma1 M)

abbrev x1FunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  x1FunctionFieldC ℚ M

def x1x0FunctionFieldC (t : ℕ) : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (Gamma1 M ⊓ Gamma0 t)


end LevelOne

section Jacobian

variable (M : ℕ)

abbrev x1FunctionFieldBar :
    IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField M)

abbrev JOne : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (x1FunctionFieldBar M)

def JOne.torsionGaloisRep (n : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End (ZMod n) (Pic0.torsion (AlgebraicClosure ℚ) (x1FunctionFieldBar M) n) :=
  (SemilinearAut.torsionRep _ _ n).comp (arithmeticGalois (x1FunctionField M))

abbrev JOneC (K : Type*) [Field K] : Type _ :=
  Pic0 K (x1FunctionFieldC K M)

end Jacobian

end ModularCurve

end
