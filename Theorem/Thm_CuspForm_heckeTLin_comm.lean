module

public import Def.ModularForm_HeckeOperatorForms

public section

namespace CuspForm

axiom heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (heckeTLin k hp hpN) (heckeTLin k hq hqN)

end CuspForm
