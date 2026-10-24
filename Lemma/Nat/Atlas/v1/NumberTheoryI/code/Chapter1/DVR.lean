import Mathlib
import sympy.Basic
open IsLocalRing Module


namespace DiscreteValuationRing

/--
[dvr_tfae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/DVR.lean)
-/
@[path]
lemma dvr_tfae
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsNoetherianRing R]
  [IsLocalRing R]
-- given
  (hR : ¬IsField R) :
-- imply
  List.TFAE [IsDiscreteValuationRing R, ValuationRing R, IsDedekindDomain R, IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime, (maximalIdeal R).IsPrincipal, finrank (ResidueField R) (CotangentSpace R) = 1, ∀ (I : Ideal R), I ≠ ⊥ → ∃ n : ℕ, I = maximalIdeal R ^ n] :=
-- proof
  IsDiscreteValuationRing.TFAE R hR

end DiscreteValuationRing


-- created on 2026-10-23
