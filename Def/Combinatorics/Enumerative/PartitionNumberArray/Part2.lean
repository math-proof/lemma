/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionNumberArray.lean -/

import Mathlib.Data.Nat.Factorial.Basic
import Structure.Combinatorics.Enumerative.PartitionNumberArray
/-!
# Partition number array (concept jis_sem_4bcead3a4bcda58a1d4dbb9f)
-/


namespace MetaMathlibExt

namespace PartitionNumberArray

/-- Part count of a partition multiplicity vector.
Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def partCount {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  countSum n p.vec

/-- Generalized Stirling numbers of the second kind via the source recurrence
with triangle conditions, so `S(k;j,1)` is concrete. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources D4
`jis_5d77e2e79b2e6bc427920b34` and P13 `jis_b4758df0448a56ca110f8d96`. -/
def genStirlingSecond (k : { k : Nat // 0 < k }) : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _m + 1 => 0
  | _n + 1, 0 => 0
  | n + 1, m + 1 =>
    ((k.val - 1) * n + (m + 1)) * genStirlingSecond k n (m + 1) +
      genStirlingSecond k n m

/-- Denominator-product recursion helper. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources M3 note
`jis_cce30bb8ff6bad04c639b7b6`, P13 `jis_b4758df0448a56ca110f8d96`, and P14
`jis_15ade3b0c1e657b464e3fd9b`. -/
def denomProdAux : Nat → (Nat → Nat) → Nat
  | 0, _ => 1
  | n + 1, g =>
    denomProdAux n g * (Nat.factorial (g n) * (Nat.factorial (n + 1)) ^ (g n))

/-- Power-product recursion helper. Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`;
sources P13 `jis_b4758df0448a56ca110f8d96` and P14
`jis_15ade3b0c1e657b464e3fd9b`. -/
def powProdAux : Nat → (Nat → Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 1
  | n + 1, g, f => powProdAux n g f * (f n) ^ (g n)

/-- Denominator product of the `M3` closed form. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources M3 note
`jis_cce30bb8ff6bad04c639b7b6`, P13 `jis_b4758df0448a56ca110f8d96`, and P14
`jis_15ade3b0c1e657b464e3fd9b`. -/
def m3DenomProd {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  denomProdAux n (extendA n p.vec)

/-- `M3` partition number as the source exact integer quotient. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources M3 note
`jis_cce30bb8ff6bad04c639b7b6`, P13 `jis_b4758df0448a56ca110f8d96`, and P14
`jis_15ade3b0c1e657b464e3fd9b`. -/
def M3 {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  Nat.factorial n / m3DenomProd p

/-- Auxiliary product of powers over a partition vector. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources P13
`jis_b4758df0448a56ca110f8d96` and P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def arrayPowProd {n : Nat} (p : PartitionMultiplicity n) (f : Fin n → Nat) : Nat :=
  powProdAux n (extendA n p.vec) (extendA n f)

/-- Hat `M32` partition number array entry. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D5
`jis_10fbc6d36dfbad8b53d9b3ee`. -/
def hatM32 (k : { k : Nat // 0 < k }) {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  arrayPowProd p (fun i => genStirlingSecond k (i.val + 1) 1)

/-- `M32` partition number array entry. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources D4
`jis_5d77e2e79b2e6bc427920b34` and P13 `jis_b4758df0448a56ca110f8d96`. -/
def M32 (k : { k : Nat // 0 < k }) {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  M3 p * hatM32 k p

/-- Absolute first-column generalized Stirling numbers of the first kind via
the source factorial quotient for positive `k`. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; source P14
`jis_15ade3b0c1e657b464e3fd9b`. -/
def stirlingFirstAbsFirstCol (k : { k : Nat // 0 < k }) (j : { j : Nat // 0 < j }) : Nat :=
  Nat.factorial (j.val + k.val - 2) / Nat.factorial (k.val - 1)

/-- `M31` partition number array entry. Concept
`jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources D7
`jis_5d8cd038f955171c2a77fec1` and P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def M31 (k : { k : Nat // 0 < k }) {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  M3 p * arrayPowProd p (fun i => stirlingFirstAbsFirstCol k ⟨i.val + 1, Nat.succ_pos _⟩)

end PartitionNumberArray
end MetaMathlibExt
