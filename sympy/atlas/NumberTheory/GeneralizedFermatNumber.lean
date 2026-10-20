/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFermatNumber.lean -/

import Mathlib.Algebra.Ring.Parity

namespace MetaMathlibExt

/-- Generalized Fermat number `Fₙ(b) = b ^ (2 ^ n) + 1` (also written `F_{b,n}`),
with `n` a positive integer and `b` even.

Source statement IDs: `jis_4d4fccc58f4ac8e97335289f` and
`jis_53ff876efdb3987b971a7ac6`; concept ID: `jis_sem_242eb546467a7c65d6fe7b54`.

Sources: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Castillo/castillo2.tex> and
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Witno/witno8.tex>.
-/
def generalizedFermatNumber (b n : ℕ) (_hb : Even b) (_hn : 0 < n) : ℕ :=
  b ^ (2 ^ n) + 1

end MetaMathlibExt
