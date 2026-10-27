/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Homothety.lean -/


import Theorem.Analysis.SpecialFunctions.Elliptic.Homothety
open scoped Pointwise


namespace PeriodPair

example (L : PeriodPair) : IsHomothetic L L :=
  IsHomothetic.refl L

example {L L' : PeriodPair} (h : IsHomothetic L L') : IsHomothetic L' L :=
  h.symm

example {L₁ L₂ L₃ : PeriodPair} (h₁₂ : IsHomothetic L₁ L₂)
    (h₂₃ : IsHomothetic L₂ L₃) : IsHomothetic L₁ L₃ :=
  h₁₂.trans h₂₃

example : Equivalence IsHomothetic :=
  isHomothetic_equivalence

example {L L' : PeriodPair} (c : ℂ) (hc : c ≠ 0)
    (hLat : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) : IsHomothetic L L' :=
  ⟨c, hc, hLat⟩

end PeriodPair
