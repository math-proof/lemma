/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/FunctionalAnalysis/LocalReflexivity.lean -/


import Theorem.Analysis.NormedSpace.LocalReflexivity.Part6


namespace MathlibExtTest.Analysis.FunctionalAnalysis.LocalReflexivity

open MathlibExt.Analysis.FunctionalAnalysis.LocalReflexivityWanted

variable {E M N : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

variable [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

variable (iM : M →L[ℝ] StrongDual ℝ (StrongDual ℝ E))

variable (iN : N →L[ℝ] StrongDual ℝ E)

variable (hM_inj : Function.Injective iM) (hN_inj : Function.Injective iN)

-- Over real scalars, the theorem yields the upper almost-isometry bound.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ T : M →L[ℝ] E, ∀ m, ‖T m‖ ≤ (1 + ε) * ‖iM m‖ := by
  obtain ⟨T, hnorm, _, _⟩ :=
    principle_of_local_reflexivity iM iN hM_inj hN_inj ε hε
  exact ⟨T, fun m => (hnorm m).2⟩

-- When `iM` lies in the canonical image of `E`, the witness recovers every preimage.
example (x : M → E)
    (hx : ∀ m, iM m = NormedSpace.inclusionInDoubleDual ℝ E (x m))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : M →L[ℝ] E, ∀ m, T m = x m := by
  obtain ⟨T, _, _, hfix⟩ :=
    principle_of_local_reflexivity iM iN hM_inj hN_inj ε hε
  exact ⟨T, fun m => hfix m (x m) (hx m)⟩

end MathlibExtTest.Analysis.FunctionalAnalysis.LocalReflexivity
