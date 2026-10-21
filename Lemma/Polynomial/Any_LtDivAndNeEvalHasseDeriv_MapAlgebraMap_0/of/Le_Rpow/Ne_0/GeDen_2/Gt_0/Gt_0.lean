import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.DvdPowSubXC.of.All_EqEvalHasseDeriv_0
import Lemma.Polynomial.DvdPowSubMulCDenXCNum
import Lemma.Polynomial.LeDiv.of.LeNatAbsLeadingCoeffRpow_DenMul.Gt_0.GeDen_2.Ne_0
import Lemma.Polynomial.NatAbsCoeff.le.RothPolyL1
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_univariate_small_hasse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (θ : ℝ)
  (P : ℤ[X])
  (q : ℚ)
  (r : ℕ)
-- given
  (hheight : (rothPolyL1 P : ℝ) ≤ Real.rpow q.den ((θ / 4) * r))
  (hPne : P ≠ 0)
  (hq : 2 ≤ q.den)
  (hr : 0 < r)
  (hθ : 0 < θ) :
-- imply
  ∃ a : ℕ, (a : ℝ) / r < θ ∧
    (hasseDeriv a (map (algebraMap ℤ ℚ) P)).eval q ≠ 0 := by
-- proof
  let k : ℕ := ⌈θ * r⌉₊
  by_contra hnot
  push Not at hnot
  have hzero : ∀ a < k,
      (hasseDeriv a (map (algebraMap ℤ ℚ) P)).eval q = 0 := by
    intro a ha
    apply hnot a
    refine (div_lt_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2 ?_
    simpa [mul_comm] using (Nat.lt_ceil.mp ha)
  have hdivQ :=
    DvdPowSubXC.of.All_EqEvalHasseDeriv_0 (map (algebraMap ℤ ℚ) P) q k hzero
  have hdiv := DvdPowSubMulCDenXCNum P q k hdivQ
  have hlead : (P.leadingCoeff.natAbs : ℝ) ≤
      Real.rpow q.den ((θ / 4) * r) := by
    refine (le_trans ?_ hheight)
    exact_mod_cast NatAbsCoeff.le.RothPolyL1 P P.natDegree
  have hindex :=
    LeDiv.of.LeNatAbsLeadingCoeffRpow_DenMul.Gt_0.GeDen_2.Ne_0
      P q k r (θ / 4) hdiv hlead hr hq hPne
  have hceil : θ ≤ (k : ℝ) / r := by
    refine (le_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2 ?_
    simpa [k, mul_comm] using (Nat.le_ceil (θ * (r : ℝ)))
  linarith


-- created on 2026-10-21
