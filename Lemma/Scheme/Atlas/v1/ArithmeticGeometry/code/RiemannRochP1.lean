import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRochP1
open RiemannRochSpace CurveDivisor CurveWithOrd


namespace RiemannRochSpace

/--
[mem_riemannRochSpace_of_prescribed_poles](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRochP1.lean)
-/
@[path]
lemma mem_riemannRochSpace_of_prescribed_poles
  {f : Fˣ}
  {A : CurveDivisor C}
-- given
  (hf : HasPrescribedPoles (C := C) (F := F) (k := k) f A) :
-- imply
  (f : F) ∈ riemannRochSpace (F := F) (k := k) A := by
-- proof
  rw [mem_riemannRochSpace_iff]
  right
  refine ⟨Units.ne_zero f, ?_⟩
  have : Units.mk0 (↑f) (Units.ne_zero f) = f := Units.mk0_val f _
  rwa [this]

end RiemannRochSpace

namespace RiemannRochSpace

/--
[degree_sub_nonneg_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRochP1.lean)
-/
@[path]
lemma degree_sub_nonneg_of_le
  {A B : CurveDivisor C}
-- given
  (hAB : A ≤ B) :
-- imply
  0 ≤ degree C B - degree C A := by
-- proof
  have hBA_eff := (CurveDivisor.le_iff_isEffective_sub A B).mp hAB
  have h0 : 0 ≤ degree C (B - A) := by
    rw [CurveDivisor.degree_eq_sum]
    exact Finsupp.sum_nonneg (fun i _ => hBA_eff i)
  linarith [degree_sub B A]
/-- Inductive step lemma for Riemann-Roch on $\mathbb{P}^1$: when $A \leq B$ are effective with $\deg B - \deg A = n$, we have $\dim_k L(B) = \dim_k L(A) + (\deg B - \deg A)$, proved by induction on $n$. -/

end RiemannRochSpace


-- created on 2026-10-23
