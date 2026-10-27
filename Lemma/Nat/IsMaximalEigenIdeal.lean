import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.HeckeGalois_EichlerShimura
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_eigenIdeal_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_eigenIdeal_isMaximal.lean)
-/
@[path]
private lemma main
  [Field k] [Finite k]
  {a : Nat.Primes → k} :
-- imply
  (ModularCurve.eigenIdeal a).IsMaximal := by
  haveI : (eigenIdeal a).IsPrime := RingHom.ker_isPrime _
  haveI : Finite (HeckeAlg ⧸ eigenIdeal a) := by
-- proof
    have e := RingHom.quotientKerEquivRange (R := HeckeAlg)
      (MvPolynomial.aeval (R := ℤ) a : HeckeAlg →ₐ[ℤ] k).toRingHom
    refine Finite.of_equiv _ e.symm.toEquiv
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)


-- created on 2026-10-23
