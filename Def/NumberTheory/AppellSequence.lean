/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AppellSequence.lean -/

import Mathlib.Algebra.Polynomial.Derivative


namespace MetaMathlibExt

/-- Classical Appell sequence over a characteristic-zero field: every polynomial
has exact `Polynomial.degree` `n` and `derivative (p (n + 1)) = C (n + 1) * p n`.
Provenance: jis_sem_73bec790e3c604ecfcaea4c0, jis_ec459310b2112700a98743da,
jis_f46aabe68ad72f828ff4cf84. -/
def IsAppellSequence {R : Type*} [Field R] [CharZero R] (p : ℕ → Polynomial R) : Prop :=
  (∀ n, Polynomial.degree (p n) = ↑n) ∧
    ∀ n, Polynomial.derivative (p (n + 1)) = Polynomial.C ((n + 1 : ℕ) : R) * p n

end MetaMathlibExt
