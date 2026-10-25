import Def.ModularCurve_ProlongationTuple
import Def.ModularCurve_ProlongationTupleSmoothPoint

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve

namespace ModularCurve

namespace PlaceSpecialization

namespace ProlongationTuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}


variable (R : ProlongationTuple P)

theorem mem_smoothLocalRingFst_iff (v : Place k (modularFunctionFieldC k N))
    (r : modularFunctionFieldBar (N * q)) :
    r ∈ R.smoothLocalRingFst v ↔
      r ∈ R.R₁.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.IsStrictFst W → P.reduceFst W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingFst, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_smoothLocalRingSnd_iff (v : Place k (modularFunctionFieldC k N))
    (r : modularFunctionFieldBar (N * q)) :
    r ∈ R.smoothLocalRingSnd v ↔
      r ∈ R.R₂.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.IsStrictSnd W → P.reduceSnd W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingSnd, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_integers_of_mem_smoothLocalRingFst {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingFst v) : r ∈ R.R₁.integers :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).1

theorem mem_integers_of_mem_smoothLocalRingSnd {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingSnd v) : r ∈ R.R₂.integers :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).1

theorem mem_toValuationSubring_of_mem_smoothLocalRingFst {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingFst v)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : P.IsStrictFst W) (hv : P.reduceFst W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).2 W hW hv

theorem mem_toValuationSubring_of_mem_smoothLocalRingSnd {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingSnd v)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : P.IsStrictSnd W) (hv : P.reduceSnd W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).2 W hW hv

end ProlongationTuple

end PlaceSpecialization

end ModularCurve

end
