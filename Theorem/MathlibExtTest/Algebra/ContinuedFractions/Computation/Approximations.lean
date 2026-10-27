/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/ContinuedFractions/Computation/Approximations.lean -/


import Lemma.Real.ContinuedFractions.Computation.Approximations


namespace GenContFract

variable {K : Type*} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [FloorRing K]

example {v : K} (n : ℕ)
    (h : ¬(GenContFract.of v).TerminatedAt (n + 1)) :
    (GenContFract.of v).dens (n + 1) <
      (GenContFract.of v).dens (n + 2) :=
  of_den_succ_lt_succ_succ n h

example {v : K}
    (h : ¬(GenContFract.of v).TerminatedAt 1) :
    (GenContFract.of v).dens 1 < (GenContFract.of v).dens 2 := by
  simpa using of_den_succ_lt_succ_succ (v := v) 0 h

example {v : K} (n : ℕ) :
    (GenContFract.of v).dens n ≤
      (GenContFract.of v).dens (n + 1) :=
  of_den_mono

example {v : K} : (GenContFract.of v).dens 0 = 1 :=
  zeroth_den_eq_one

end GenContFract
