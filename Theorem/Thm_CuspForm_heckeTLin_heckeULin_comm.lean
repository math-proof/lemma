module

public import Def.ModularForm_HeckeOperatorForms

public section

namespace CuspForm

axiom heckeTLin_heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (heckeTLin k hp hpN) (heckeULin k hqN)

end CuspForm
