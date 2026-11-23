module

public import Mathlib

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MvFormalGroup

namespace WittLaw

variable (p : ℕ)

def weight {idx : Type*} (c : idx → ℕ) : idx × ℕ → ℕ := fun im => c im.1 * p ^ im.2

end WittLaw

end MvFormalGroup

end

end
