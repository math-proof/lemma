import Mathlib
import Instance.Module_CommFamilyAnnPart

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace Module.End

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] (σ : Type*)

structure CommFamily where

  T : σ → Module.End K V

  comm : ∀ a b : σ, Commute (T a) (T b)

variable {K V σ}

namespace CommFamily

variable (F : CommFamily K V σ)


end CommFamily

end Module.End
