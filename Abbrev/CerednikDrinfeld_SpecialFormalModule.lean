module

public import Mathlib

set_option autoImplicit false

@[expose] public noncomputable section

namespace CerednikDrinfeld

variable (p : ℕ) [Fact p.Prime]

abbrev Zp2 : Type := WittVector p (GaloisField p 2)

end CerednikDrinfeld

end
