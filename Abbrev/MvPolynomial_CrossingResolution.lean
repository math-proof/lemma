import Mathlib
import Abbrev.MvPolynomial_CrossingQuotient

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type*} [CommRing W] (t : W)

abbrev U : CrossingQuotient W t := mk t (X 0)

abbrev V : CrossingQuotient W t := mk t (X 1)

end CrossingQuotient

end MvPolynomial

end
