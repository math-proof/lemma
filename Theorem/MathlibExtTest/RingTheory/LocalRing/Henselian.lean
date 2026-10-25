/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/Henselian.lean -/


import Lemma.Int.LocalRing.Henselian
open IsLocalRing Polynomial

variable (R : Type*) [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]


example : HenselianLocalRing R :=
  HenselianLocalRing.of_isAdicComplete_maximalIdeal R

example :
    ∀ (f : R[X]), f.Monic → ∀ a0 : ResidueField R,
      Polynomial.aeval a0 f = 0 →
      Polynomial.aeval a0 f.derivative ≠ 0 →
      ∃ a : R, f.IsRoot a ∧ residue R a = a0 := by
  let : HenselianLocalRing R :=
    HenselianLocalRing.of_isAdicComplete_maximalIdeal R
  exact ((HenselianLocalRing.TFAE R).out 1 2).mp
    (inferInstance : HenselianLocalRing R)

example (f : R[X]) (hf : f.Monic) (a0 : R)
    (hroot : f.eval a0 ∈ maximalIdeal R)
    (hderiv : IsUnit (f.derivative.eval a0)) :
    ∃ a : R, f.IsRoot a ∧ a - a0 ∈ maximalIdeal R := by
  let : HenselianLocalRing R :=
    HenselianLocalRing.of_isAdicComplete_maximalIdeal R
  exact HenselianLocalRing.is_henselian f hf a0 hroot hderiv

