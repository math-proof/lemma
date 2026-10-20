/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NStepLucasSequence.lean -/

import Mathlib.Data.List.Basic

/-!
# n-step Lucas sequence

Formalizes the `n`-step Lucas sequence from Saito (JIS VOL14).
See `nStepLucas` for the indexed sequence and `nStepLucasList`
for the finite-prefix computation.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex>.
-/

namespace MetaMathlibExt

/-- Finite prefixes of the `n`-step Lucas sequence (source `jis_1628603e2683fb05481e5bfb`,
concept `jis_sem_4e0294575601a2b8a5f0d3d7`): `nStepLucasList n m = [L_1^n, …, L_m^n]`,
where `L_k^n = 2 ^ k - 1` for `1 ≤ k ≤ n` and `L_k^n` is the sum of the previous
`n` terms for `k ≥ n + 1`. -/
def nStepLucasList (n : ℕ) : ℕ → List ℕ
  | Nat.zero => []
  | Nat.succ m =>
    let prev := nStepLucasList n m
    let next :=
      if m + 1 ≤ n then 2 ^ (m + 1) - 1
      else (prev.drop (prev.length - n)).foldl (· + ·) 0
    prev ++ [next]

/-- `n`-step Lucas sequence (source `jis_1628603e2683fb05481e5bfb`, concept
`jis_sem_4e0294575601a2b8a5f0d3d7`): for `n ≥ 1`, `nStepLucas n m = 2 ^ m - 1`
for `1 ≤ m ≤ n` and `nStepLucas n m` is the sum of the `n` preceding values for
`m ≥ n + 1`; by convention `nStepLucas 0 m = 0` for all `m`, and
`nStepLucas n 0 = 0` as the totalization at `m = 0` outside the source domain
`m ≥ 1`. -/
def nStepLucas (n m : ℕ) : ℕ :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => (nStepLucasList (n + 1) m).getLast?.getD 0

end MetaMathlibExt
