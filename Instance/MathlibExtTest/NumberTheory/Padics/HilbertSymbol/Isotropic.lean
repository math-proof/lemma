/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/HilbertSymbol/Isotropic.lean -/


import Lemma.Nat.Padics.HilbertSymbol.Isotropic
set_option autoImplicit false


/-!
# Tests for isotropy of unit diagonal forms over `ℚ_[p]`
-/


namespace HilbertSymbol

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

end HilbertSymbol
