import Lemma.Definitions.Def_ModularCurve_JHNodeDepthInf

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

structure TwistVec (ι : Type*) where

  aZ : ℤ

  aZ' : ℤ

  aE : ι → ℕ → ℤ

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

def AnnulusPositionLaw : Prop :=
  ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom →
    0 < pos s V ∧ pos s V < e s ∧
      A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * ((An s).param)⁻¹)) ^ (pos s V).den =
        A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ (pos s V).num.toNat

def twistChainVal (a : TwistVec ↥SS) (s : ↥SS) (d : ℕ) : ℤ :=
  if d = 0 then a.aZ else if e s ≤ d then a.aZ' else a.aE s d

open Classical in

def twistCircleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) (d : ℕ) : ℚ :=
  ∑ V ∈ D.support with V ∈ (An s).dom, (D V : ℚ) * max 0 (1 - |pos s V - d|)

def twistEndShareFst (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  if (twistCircleDeg SS An pos D s 0).den = 1 then (twistCircleDeg SS An pos D s 0).num else 0

def twistEndShareSnd (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  if (twistCircleDeg SS An pos D s (e s)).den = 1 then (twistCircleDeg SS An pos D s (e s)).num else 0

def twistEndOrderFst (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  (twistChainVal SS e a s 1 - twistChainVal SS e a s 0) + twistEndShareFst SS An pos D s

def twistEndOrderSnd (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  (twistChainVal SS e a s (e s - 1) - twistChainVal SS e a s (e s)) + twistEndShareSnd SS e An pos D s

def IsTwistOf (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Prop :=
  Divisor.degree (Psp.fstDiv α β hα hβ δ D) = -∑ s : ↥SS, twistEndOrderFst SS e An pos a D s ∧
    Divisor.degree (Psp.sndDiv α β hα hβ δ D) = -∑ s : ↥SS, twistEndOrderSnd SS e An pos a D s ∧
    ∀ (s : ↥SS) (d : ℕ), 1 ≤ d → d + 1 ≤ e s →
      twistCircleDeg SS An pos D s d =
        -((twistChainVal SS e a s (d - 1) - 2 * twistChainVal SS e a s d + twistChainVal SS e a s (d + 1) : ℤ) : ℚ)

def IsTwistType (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Prop :=
  ∃ a : TwistVec ↥SS, Psp.IsTwistOf α β hα hβ δ SS e An pos a D

end

end JHPlaceSpecialization
end ModularCurve

end
