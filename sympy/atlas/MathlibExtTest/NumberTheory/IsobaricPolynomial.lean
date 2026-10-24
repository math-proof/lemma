/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/IsobaricPolynomial.lean -/


import sympy.atlas.NumberTheory.IsobaricPolynomial

namespace MetaMathlibExt

noncomputable section

example {k : ℕ} (d : Fin k →₀ ℕ) :
    isobaricWeight d = Finsupp.weight (fun j : Fin k ↦ j.val + 1) d := rfl

example {k n : ℕ} : IsIsobaric n (0 : MvPolynomial (Fin k) ℤ) :=
  MvPolynomial.isWeightedHomogeneous_zero ℤ (fun j : Fin k ↦ j.val + 1) n

example {k : ℕ} (i : Fin k) :
    IsIsobaric (i.val + 1) (MvPolynomial.X i : MvPolynomial (Fin k) ℤ) :=
  MvPolynomial.isWeightedHomogeneous_X ℤ (fun j : Fin k ↦ j.val + 1) i

end

end MetaMathlibExt
