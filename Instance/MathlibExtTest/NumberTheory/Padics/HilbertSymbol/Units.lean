/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/HilbertSymbol/Units.lean -/


module

public import Def.NumberTheory.Padics.HilbertSymbol.Units
public import Theorem.Nat.Padics.HilbertSymbol.Units
@[expose] public section

set_option autoImplicit false


/-!
# Tests for Hilbert symbols of p-adic integer units
-/


namespace HilbertSymbol

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

end HilbertSymbol
