import Lemma.ModularCurve.AtkinLehner
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Height.NumberField
import Instance.Compat_Mathlib430
import Instance.ModularCurve_JZeroNaiveHeight

noncomputable section

open AlgebraicCurve Polynomial

namespace ModularCurve

variable (N : ℕ) [NeZero N]

def jCoord (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : AlgebraicClosure ℚ :=
  Classical.epsilon fun c : AlgebraicClosure ℚ =>
    0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)

def jFactor (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Polynomial (AlgebraicClosure ℚ) :=
  if 0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
  then X - C (jCoord N v) else 1

def symPoly (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Polynomial (AlgebraicClosure ℚ) :=
  D.prod fun v n => jFactor N v ^ n.toNat

def symVec (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Fin (g' + 1) → AlgebraicClosure ℚ :=
  fun k => (symPoly N D).coeff (g' - k)

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

open scoped Classical in

def divNaiveHeight (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  if h : ∀ k, symVec N g' D k ∈ K then Height.logHeight fun k => (⟨symVec N g' D k, h k⟩ : K) else 0

def JZero.repHeights (g' : ℕ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup)) : Set ℝ :=
  {r | ∃ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
      (∀ v, 0 ≤ D v) ∧
      (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
          + (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
          arithmeticGalois (modularFunctionFieldFull N) σ • D = D) ∧
      Pic0.mk E = (c : JZero N) ∧
      r = divNaiveHeight N K g' D}

def JZero.naiveHeight (g' : ℕ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup)) : ℝ :=
  sInf (JZero.repHeights N K g' c)

end ModularCurve

end
