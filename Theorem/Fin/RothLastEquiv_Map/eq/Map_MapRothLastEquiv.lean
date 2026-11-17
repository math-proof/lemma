module

public import Mathlib
public import Theorem.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastEquiv_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothLastEquiv_Map.eq.Map_MapRothLastEquiv
  {n : ℕ} [CommSemiring R] [CommSemiring S]
-- given
  (f : R →+* S)
  (P : MvPolynomial (Fin (n + 1)) R) :
-- imply
  rothLastEquiv S n (MvPolynomial.map f P) =
    Polynomial.map (MvPolynomial.map f) (rothLastEquiv R n P) := by
-- proof
  ext a i
  rw [CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex,
    MvPolynomial.coeff_map, Polynomial.coeff_map, MvPolynomial.coeff_map,
    CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex]


-- created on 2026-10-21
