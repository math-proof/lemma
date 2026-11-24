module
public import Theorem.Finsupp.JZeroNaiveHeight
public import Def.AlgebraicCurve_PlaceEvaluation
public import Theorem.Submodule.Repartitions
public import Theorem.Ideal.Mathlib430


public section

noncomputable section

open AlgebraicCurve Submodule

namespace AlgebraicCurve

def absLogHeight {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : ℝ :=
  haveI := finiteDimensional_adjoin_range x
  (Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) : ℝ)⁻¹ *
    Height.logHeight fun i =>
      (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range x))

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

open Classical in

def pivotIndex {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) : Fin r :=
  if h : ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) then Classical.choose h else ⟨0, hr⟩

open Classical in

def evalVec {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    Fin r → AlgebraicClosure ℚ :=
  fun i => if hr : 0 < r then v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) else 0

def chordVec {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    Fin r × Fin r → AlgebraicClosure ℚ :=
  fun p => evalVec s v p.1 * evalVec s w p.2 - evalVec s v p.2 * evalVec s w p.1

def pointHt {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) : ℝ :=
  absLogHeight (evalVec s v)

def pairHt {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) : ℝ :=
  pointHt s v + pointHt s w - absLogHeight (chordVec s v w)

open Classical in

def baseHt {r : ℕ} (s : Fin r → F) (b v : Place (AlgebraicClosure ℚ) F) : ℝ :=
  if v = b then 0 else pairHt s v b

def heightFormAux {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) : ℝ :=
  ((γ : ℝ) + (D.sum fun _ n => (n : ℝ)) - 1) * (D.sum fun v n => (n : ℝ) * baseHt s b v)
    - (∑ p ∈ D.support.offDiag, ((D p.1 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2) / 2
    - (2 - 2 * (γ : ℝ)) * (D.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * baseHt s b v)

def heightForm {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) : ℝ :=
  heightFormAux s γ b (D.erase b)

end AlgebraicCurve

namespace ModularCurve

variable (N : ℕ) [NeZero N]

def embDegree : ℕ :=
  2 * genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) + 1

def embDivisor : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  (embDegree N : ℤ) • Finsupp.single (cuspInftyBar N) 1

def IsEmbBasis {r : ℕ} (s : Fin r → modularFunctionFieldBar N) : Prop :=
  LinearIndependent (AlgebraicClosure ℚ) s ∧
    Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace (embDivisor N)

def JZero.heightForm {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  AlgebraicCurve.heightForm s (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (cuspInftyBar N) D

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

def JZero.IsRepOf (n : ℕ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : Prop :=
  ∃ E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)),
    (∀ v, 0 ≤ D v) ∧
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        + (n : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
        arithmeticGalois (modularFunctionFieldFull N) σ • D = D) ∧
    Pic0.mk E = (c : JZero N)

variable {N K}

omit [FiniteDimensional ℚ K] in

end ModularCurve

end
