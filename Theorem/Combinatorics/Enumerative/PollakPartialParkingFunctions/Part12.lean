/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part11


namespace MetaMathlibExt.PollakPartialParking

/-- Double count, grouped by preference function. -/
theorem card_circle_pairs (s t : ℕ) (hst : s ≤ t) :
    Fintype.card {p : (Fin s → ZMod (t + 1)) × ZMod (t + 1) //
      p.2 ∈ parkEmpty s t p.1 hst} = (t + 1 - s) * (t + 1) ^ s := by
  have : NeZero (t + 1) := ⟨by omega⟩
  have hdom : Fintype.card (Fin s → ZMod (t + 1)) = (t + 1) ^ s := by
    rw [Fintype.card_pi_const, ZMod.card]
  have e := Fintype.card_congr (StoSigma s t hst)
  rw [e, Fintype.card_sigma]
  have hsum : (∑ g : (Fin s → ZMod (t + 1)),
        Fintype.card ↥(parkEmpty s t g hst)) =
      ∑ _g : (Fin s → ZMod (t + 1)), (t + 1 - s) :=
    Finset.sum_congr rfl (fun g _ => by
      rw [Fintype.card_coe, card_parkEmpty s t g hst])
  rw [hsum, Finset.sum_const, Finset.card_univ, hdom, smul_eq_mul]
  ring

/-- Pollak's circle trick for partial parking functions: for positive `s ≤ t`,
the number of preference lists `f : Fin s → Fin t` satisfying the standard
successful-parking threshold characterization (for every zero-based spot `k`,
at most `t - k` cars prefer a spot at or after `k`) is
`(t + 1 - s) * (t + 1) ^ (s - 1)`.

Provenance (independently verified):

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and
  Marshall Moats, “Lucky Cars and Lucky Spots in Parking Functions”,
  Journal of Integer Sequences 29 (2026), Article 26.1.1.
- Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex
- Proposition at source lines 330–332.
- Full source SHA-256:
  d166e7759bfd986aebf8bd5632479d9f5e4f11b28f5250ed1e5290851a8d6139
- Normalized no-final-newline proposition-span SHA-256:
  58e90130ad683625acf4a657d5bbbf145f2700065e2991cfd7084425783cc1fe

Proves `Wanted` entry `pollak_partial_parking_functions_card`.
-/
theorem pollak_partial_parking_functions_card
    (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) :
    Nat.card {f : Fin s → Fin t // IsPartialParkingFunction s t f} =
    (t + 1 - s) * (t + 1) ^ (s - 1) := by
  have : NeZero (t + 1) := ⟨by omega⟩
  have hPf : Nat.card {f : Fin s → Fin t // IsPartialParkingFunction s t f} =
      Nat.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} :=
    Nat.card_congr (PfEquiv s t hst)
  have hS := card_circle_pairs s t hst
  have hT := card_circle_fibers s t hst
  have hST : Fintype.card {p : (Fin s → ZMod (t + 1)) × ZMod (t + 1) //
        p.2 ∈ parkEmpty s t p.1 hst} =
      Fintype.card {p : ZMod (t + 1) × (Fin s → ZMod (t + 1)) //
        p.1 ∈ parkEmpty s t p.2 hst} :=
    Fintype.card_congr ((Equiv.prodComm _ _).subtypeEquiv (fun _ => Iff.rfl))
  have hG : Nat.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} =
      Fintype.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} :=
    Nat.card_eq_fintype_card
  rw [hPf, hG]
  have heq : (t + 1) * Fintype.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} = (t + 1 - s) * (t + 1) ^ s := by
    rw [← hT, ← hS]
    exact hST.symm
  have hpow : (t + 1) ^ s = (t + 1) * (t + 1) ^ (s - 1) := by
    have hs1 : s = (s - 1) + 1 := by omega
    conv_lhs => rw [hs1, pow_succ]
    exact mul_comm _ _
  have hfin : Fintype.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} = (t + 1 - s) * (t + 1) ^ (s - 1) := by
    have h := heq
    rw [hpow] at h
    have hassoc : (t + 1 - s) * ((t + 1) * (t + 1) ^ (s - 1)) =
        (t + 1) * ((t + 1 - s) * (t + 1) ^ (s - 1)) := by ring
    rw [hassoc] at h
    exact Nat.mul_left_cancel (Nat.succ_pos t) h
  exact hfin

end MetaMathlibExt.PollakPartialParking
