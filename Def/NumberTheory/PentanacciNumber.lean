/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PentanacciNumber.lean -/

import Mathlib.Data.Nat.Basic


namespace MetaMathlibExt

/-- Pentanacci numbers: the order-5 higher-order (generalized) Fibonacci sequence
    with ordinary generating function `1 / (1 - t - t^2 - t^3 - t^4 - t^5)`
    (OEIS A001591). Each term from index 5 onward is the sum of the five
    immediately preceding terms, with initial values `1, 1, 2, 4, 8`.
    Concept `jis_sem_a98a2c489e24a91907e84283`; source statements
    `jis_6eb337f276c191430742e49f`, `jis_cb7e03aa435f1bbd253660ca`,
    `jis_f311834ff91269ae7cf94a4b`. -/
def pentanacciNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 8
  | n + 5 =>
      pentanacciNumber (n + 4) + pentanacciNumber (n + 3) +
        pentanacciNumber (n + 2) + pentanacciNumber (n + 1) +
        pentanacciNumber n

end MetaMathlibExt
