module

public import Def.ModularForm_HeckeOperatorForms

public section

namespace CuspForm

axiom heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hpN : p ∣ N) (hqN : q ∣ N) :
    Commute (heckeULin k hpN) (heckeULin k hqN)

end CuspForm
