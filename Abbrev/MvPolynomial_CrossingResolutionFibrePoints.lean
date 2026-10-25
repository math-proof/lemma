import Mathlib
import Instance.MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 200000
set_option autoImplicit false

noncomputable section

open Polynomial LaurentPolynomial

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W)

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open Polynomial

universe u

variable {W : Type u} [CommRing W] (t : W)

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)
include ht

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open Polynomial

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)

section lineU

abbrev IU : Ideal (CrossingQuotient W t) := Ideal.span {U t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t))

end lineU

section lineV

abbrev IV : Ideal (CrossingQuotient W t) := Ideal.span {V t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t))

end lineV

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open AlgebraicGeometry CategoryTheory GlueIndex

universe u

variable {W : Type u} [CommRing W] (t : W)

namespace Resolution

variable (e : ℕ)

end Resolution

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace V3Glue.Aux

open Topology

end V3Glue.Aux

namespace MvPolynomial.CrossingQuotient.Resolution

open AlgebraicGeometry CategoryTheory GlueIndex V3Glue.Aux

universe u

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

section maximal
variable [𝔭.IsMaximal]

end maximal

end MvPolynomial.CrossingQuotient.Resolution

end

noncomputable section

namespace MvPolynomial.CrossingQuotient.Resolution

open AlgebraicGeometry CategoryTheory

universe u

variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

end MvPolynomial.CrossingQuotient.Resolution

end
