import Mathlib
import Lemma.Int.FaithfullyFlat
open Int
open scoped TensorProduct


/--
[Algebra_Etale_of_etale_adicCompletion_tensorProduct](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_of_etale_adicCompletion_tensorProduct.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
-- given
  (h : Algebra.Etale (AdicCompletion (IsLocalRing.maximalIdeal R) R)
    ((AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗[R] S)) :
-- imply
  Algebra.Etale R S := by
-- proof
  have := h
  have := FaithfullyFlat (R := R)
  apply Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat
    (AdicCompletion (IsLocalRing.maximalIdeal R) R)


-- created on 2026-10-12
