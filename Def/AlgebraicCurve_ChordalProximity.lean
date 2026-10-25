import Lemma.ModularCurve.JZeroHeightForm

noncomputable section

namespace AlgebraicCurve

def prox {L : Type*} {ι : Type*} [Mul L] [Sub L] (ν : L → ℝ) (x y : ι → L) : ℝ :=
  Real.log (⨆ i, ν (x i)) + Real.log (⨆ i, ν (y i))
    - Real.log (⨆ p : ι × ι, ν (x p.1 * y p.2 - x p.2 * y p.1))

open Classical in

def secVal {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (v : Place (AlgebraicClosure ℚ) F) (k : ℕ) (u : F) : AlgebraicClosure ℚ :=
  if hr : 0 < r then v.evalAt (u * ((s (pivotIndex s v hr))⁻¹) ^ k) else 0

open Classical in

def regVal {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (o : Place (AlgebraicClosure ℚ) F) (t : F) (k e : ℕ) (u : F) : AlgebraicClosure ℚ :=
  if hr : 0 < r then o.evalAt (u * ((s (pivotIndex s o hr))⁻¹) ^ k * (t⁻¹) ^ e) else 0

end AlgebraicCurve

end
