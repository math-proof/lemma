/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/HilbertSymbol/Units.lean -/


import Def.NumberTheory.Padics.HilbertSymbol.Units
import Lemma.Nat.Padics.HilbertSymbol.Units
set_option autoImplicit false


/-!
# Tests for Hilbert symbols of p-adic integer units
-/


namespace HilbertSymbol

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

end HilbertSymbol
