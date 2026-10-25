import Lemma.ModularCurve.ModuliPoint
import Def.ModularCurve_MazurStepThreeInputs

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

section PairStab

variable {N : ℕ} {L : Type*} [Field L] [DecidableEq L]

noncomputable def pairStabCard (P : Gamma0Pair N L) : ℕ :=
  Nat.card {γ : VariableChange L // γ • P.toCurve = P.toCurve ∧
    ∃ k : ℕ, k.Coprime N ∧ HEq P.gen (k • Point.vcInvFun γ P.toCurve.toAffine P.gen)}

end PairStab

def Emb (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ) : Type :=
  {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ) //
    ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)}

def Induces {N : ℕ} [NeZero N]
    (ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ))
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) : Prop :=
  ∃ g : ℚ, 0 < g ∧ ∀ x : ↥(modularFunctionFieldBar N), (w.ord x : ℚ) * g = (ψ x).order

def SamePlace {N : ℕ} [NeZero N]
    (ψ ψ' : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ)) :
    Prop :=
  ∃ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), Induces ψ w ∧ Induces ψ' w

def CycSub (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (N : ℕ) : Type :=
  {H : AddSubgroup E₀.toAffine.Point //
    ∃ g : E₀.toAffine.Point, addOrderOf g = N ∧ H = AddSubgroup.zmultiples g}

def SameOrbit (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (H H' : AddSubgroup E₀.toAffine.Point) :
    Prop :=
  ∃ γ : VariableChange (AlgebraicClosure ℚ), ∃ _ : γ • E₀ = E₀, ∃ g g' : E₀.toAffine.Point,
    H = AddSubgroup.zmultiples g ∧ H' = AddSubgroup.zmultiples g' ∧
      HEq g' (Point.vcInvFun γ E₀.toAffine g)

def EMD (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ) : Prop :=
  ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
    ∃ Φ : Emb N j₀ ≃ CycSub E₀ N, ∀ ψ ψ' : Emb N j₀,
      SamePlace ψ.1 ψ'.1 ↔ SameOrbit E₀ (Φ ψ).1 (Φ ψ').1

end ModularCurve

end
