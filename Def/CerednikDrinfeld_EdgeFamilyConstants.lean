import Mathlib
import Instance.CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Abbrev.CerednikDrinfeld_EdgeFamilyConstants

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld
namespace EdgeFamily

variable (p : ℕ) [Fact p.Prime]

def wittDigit {R : Type*} [CommRing R] (x : R) (j : ℕ) : R :=
  (WittVector.frobenius (WittVector.teichmuller p x) - WittVector.teichmuller p x).coeff j

def branchConstants {R : Type*} [CommRing R] (x : R) (m : ℕ) : R :=
  if m = 0 then x ^ p - x
  else if m = 1 then 1
  else if m % 2 = 0 then wittDigit p x (m / 2) ^ p ^ (m / 2)
  else 0

def edgeConstants {R : Type*} [CommRing R] (ξ η : R) : ℕ → Fin 2 → R :=
  fun m i => if i = 0 then branchConstants p η m else branchConstants p ξ m

end EdgeFamily

end CerednikDrinfeld

end
