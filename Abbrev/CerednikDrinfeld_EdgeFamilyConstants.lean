import Mathlib
import Instance.CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld
namespace EdgeFamily

variable (p : ℕ) [Fact p.Prime]


abbrev edgeRingCharP (k : Type) [CommRing k] : Type := FormalOmega.chartERing k (0 : k) p

abbrev edgeRingCharP.ξ (k : Type) [CommRing k] : edgeRingCharP p k := FormalOmega.chartERing.ξ k (0 : k) p

abbrev edgeRingCharP.η (k : Type) [CommRing k] : edgeRingCharP p k := FormalOmega.chartERing.η k (0 : k) p

omit [Fact p.Prime] in


end EdgeFamily
end CerednikDrinfeld

end

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld
namespace EdgeFamily

variable (p : ℕ) [Fact p.Prime]


variable {p}


abbrev edgeRingConstants (k : Type) [CommRing k] : ℕ → Fin 2 → edgeRingCharP p k :=
  edgeConstants p (edgeRingCharP.ξ p k) (edgeRingCharP.η p k)

end EdgeFamily

end CerednikDrinfeld

end
