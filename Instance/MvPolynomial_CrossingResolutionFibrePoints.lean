-- Carved from Lemma/Definitions/Def_MvPolynomial_CrossingResolutionFibrePoints.lean: instance decls only.
import Mathlib
import Instance.MvPolynomial_CrossingResolutionScheme
import Lemma.MvPolynomial.CrossingResolutionFibrePoints

set_option maxHeartbeats 200000
set_option autoImplicit false

noncomputable section

open Polynomial LaurentPolynomial

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W)

variable (ht : t ∈ 𝔭)

instance isPrime_originIdeal [𝔭.IsPrime] : (originIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _
instance isPrime_lineVIdeal [𝔭.IsPrime] : (lineVIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _
instance isPrime_lineUIdeal [𝔭.IsPrime] : (lineUIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _

instance isPrime_overlapIdeal [𝔭.IsPrime] : (overlapIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _

variable (e : ℕ)

end MvPolynomial.CrossingQuotient

end


noncomputable section

namespace MvPolynomial.CrossingQuotient

open AlgebraicGeometry CategoryTheory GlueIndex

universe u

variable {W : Type u} [CommRing W] (t : W)

namespace Resolution

variable (e : ℕ)

variable (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

instance isPrime_vertexIdeal (he : 1 ≤ e) : (vertexIdeal t 𝔭 ht e he).IsPrime := isPrime_originIdeal _ _ _
instance isPrime_branchVPrime (he : 1 ≤ e) : (branchVPrime t 𝔭 ht e he).IsPrime := isPrime_lineVIdeal _ _ _
instance isPrime_branchUPrime (he : 1 ≤ e) : (branchUPrime t 𝔭 ht e he).IsPrime := isPrime_lineUIdeal _ _ _

end Resolution

end MvPolynomial.CrossingQuotient

end


