/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/GeneralizedHypergeometric.lean -/


import sympy.atlas.Analysis.SpecialFunctions.GeneralizedHypergeometric
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt.GeneralizedHypergeometric

example {K : Type*} [Field K] (x : K) :
    generalizedHypergeometricCoefficient ({x} : Multiset K) 0 1 = x := by
  simp [generalizedHypergeometricCoefficient]

example :
    generalizedHypergeometricCoefficient ({2} : Multiset ℚ) {3} 2 = 1 / 4 := by
  norm_num [generalizedHypergeometricCoefficient, ascPochhammer]

example : generalizedHypergeometricCoefficient ({2} : Multiset ℚ) {0} 1 = 0 := by
  norm_num [generalizedHypergeometricCoefficient, ascPochhammer]

end MetaMathlibExt.GeneralizedHypergeometric

namespace MetaMathlibExt.GeneralizedHypergeometricTest

open MetaMathlibExt.GeneralizedHypergeometric

example : LowerParametersAdmissible ({(5 : ℂ) + Complex.I} : Multiset ℂ) := by
  intro k h
  have heq := Multiset.mem_singleton.mp h
  have him : ((-↑k : ℂ)).im = ((5 : ℂ) + Complex.I).im :=
    congrArg Complex.im heq
  simp at him

example (hadm : LowerParametersAdmissible ({(5 : ℂ) + Complex.I} : Multiset ℂ))
    (n : ℕ) :
    (ascPochhammer ℂ n).eval ((5 : ℂ) + Complex.I) ≠ 0 :=
  lowerParametersAdmissible_ascPochhammer_ne_zero hadm (by simp) n

example (hadm : LowerParametersAdmissible ({(5 : ℂ) + Complex.I} : Multiset ℂ)) :
    ∀ b ∈ ({(5 : ℂ) + Complex.I} : Multiset ℂ), ∀ n : ℕ,
      (ascPochhammer ℂ n).eval b ≠ 0 :=
  lowerParametersAdmissible_forall_mem_ne_zero hadm

example :
    generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 3 = 0 := by
  have hmem : (-(2 : ℂ) ∈ ({-(2 : ℂ)} : Multiset ℂ)) := by simp
  exact generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper
    ({-(2 : ℂ)} : Multiset ℂ) 0 (k := 2) (by omega) hmem

example :
    generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 5 = 0 := by
  have hmem : (-(2 : ℂ) ∈ ({-(2 : ℂ)} : Multiset ℂ)) := by simp
  exact generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper
    ({-(2 : ℂ)} : Multiset ℂ) 0 (k := 2) (by omega) hmem

example (z : ℂ) :
    SummableHypergeometric ({-(2 : ℂ)} : Multiset ℂ) 0 z := by
  have hmem : (-(2 : ℂ) ∈ ({-(2 : ℂ)} : Multiset ℂ)) := by simp
  exact summableHypergeometric_of_neg_coe_nat_mem_upper (N := 2) hmem

example (z : ℂ)
    (hsum : SummableHypergeometric ({-(2 : ℂ)} : Multiset ℂ) 0 z) :
    HasSum
      (fun n : ℕ =>
        generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 n *
          z ^ n)
      (generalizedHypergeometricValue ({-(2 : ℂ)} : Multiset ℂ) 0 z) :=
  generalizedHypergeometricValue_hasSum hsum

example (a b : Multiset ℂ) (z : ℂ) :
    generalizedHypergeometricValue a b z =
      ∑' n, generalizedHypergeometricCoefficient a b n * z ^ n :=
  generalizedHypergeometricValue_eq_tsum a b z

example (z : ℂ) :
    (∑' n : ℕ,
        generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 n *
          z ^ n) =
      ∑ n ∈ Finset.range 3,
        generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 n *
          z ^ n := by
  have hmem : (-(2 : ℂ) ∈ ({-(2 : ℂ)} : Multiset ℂ)) := by simp
  exact generalizedHypergeometric_tsum_eq_finset_sum (N := 2) (z := z) hmem

example (z : ℂ) :
    generalizedHypergeometricValue ({-(2 : ℂ)} : Multiset ℂ) 0 z =
      ∑ n ∈ Finset.range 3,
        generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 n *
          z ^ n := by
  have hmem : (-(2 : ℂ) ∈ ({-(2 : ℂ)} : Multiset ℂ)) := by simp
  exact generalizedHypergeometricValue_terminating_eq_finset_sum (N := 2) hmem

example : ¬ LowerParametersAdmissible ({(0 : ℂ)} : Multiset ℂ) := by
  intro h
  have h0 := h 0
  simp at h0

example : ¬ LowerParametersAdmissible ({-(1 : ℂ)} : Multiset ℂ) := by
  intro h
  have h1 := h 1
  simp at h1

example : ¬ LowerParametersAdmissible ({-(3 : ℂ), (2 : ℂ)} : Multiset ℂ) := by
  intro h
  have h3 := h 3
  simp at h3

example :
    generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 2 ≠ 0 := by
  have h :
      generalizedHypergeometricCoefficient ({-(2 : ℂ)} : Multiset ℂ) 0 2 = 1 := by
    norm_num [generalizedHypergeometricCoefficient, ascPochhammer]
  rw [h]
  exact one_ne_zero

example :
    generalizedHypergeometricCoefficient 0 ({(0 : ℂ)} : Multiset ℂ) 1 = 0 := by
  have hmem : ((0 : ℂ) ∈ ({(0 : ℂ)} : Multiset ℂ)) := by simp
  exact generalizedHypergeometricCoefficient_eq_zero_of_zero_mem_lower
    0 ({(0 : ℂ)} : Multiset ℂ) (by omega) hmem

example :
    generalizedHypergeometricCoefficient 0 ({-((1 : ℕ) : ℂ)} : Multiset ℂ) 2 =
      0 := by
  have hmem : (-((1 : ℕ) : ℂ) ∈ ({-((1 : ℕ) : ℂ)} : Multiset ℂ)) := by simp
  exact generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower
    0 ({-((1 : ℕ) : ℂ)} : Multiset ℂ) (k := 1) (by omega) hmem

end MetaMathlibExt.GeneralizedHypergeometricTest
