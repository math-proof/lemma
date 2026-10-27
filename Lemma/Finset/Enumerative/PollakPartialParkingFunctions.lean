import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part12
open MetaMathlibExt.PollakPartialParking


namespace MetaMathlibExt.PollakPartialParking

/--
[firstFree_is_ray](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean)
-/
@[path]
private lemma firstFree_is_ray (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
  (h : occ.card < t + 1) :
  ∃ j : ℕ, firstFree t occ a h = a + (((j : ℕ)) : ZMod (t + 1)) :=
  ⟨_, rfl⟩

end MetaMathlibExt.PollakPartialParking

namespace MetaMathlibExt.PollakPartialParking

/--
[linOccAux_succ_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean)
-/
@[path]
private lemma linOccAux_succ_ge (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
  (occ : { occ : Finset (Fin t) // occ.card ≤ n })
  (hm : linOccAux s t f n = some occ) (h : ¬ n < s) :
  linOccAux s t f (n + 1) = some ⟨occ.val, le_trans occ.property (Nat.le_succ n)⟩ := by
  simp only [linOccAux, hm, h, dite_false]

end MetaMathlibExt.PollakPartialParking

namespace MetaMathlibExt.PollakPartialParking

/--
[card_circle_fibers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean)
-/
@[path]
private lemma card_circle_fibers (s t : ℕ) (hst : s ≤ t) :
  Fintype.card {p : ZMod (t + 1) × (Fin s → ZMod (t + 1)) //
    p.1 ∈ parkEmpty s t p.2 hst} =
  (t + 1) * Fintype.card
    {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} := by
  have : NeZero (t + 1) := ⟨by omega⟩
  have e := Fintype.card_congr (TtoSigma s t hst)
  rw [e, Fintype.card_sigma]
  have hsum : (∑ x : ZMod (t + 1),
    Fintype.card {g : Fin s → ZMod (t + 1) // x ∈ parkEmpty s t g hst}) =
    ∑ _x : ZMod (t + 1), Fintype.card
      {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} :=
    Finset.sum_congr rfl (fun x _ => Fintype.card_congr (fiberEquiv s t hst x))
  rw [hsum, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]

end MetaMathlibExt.PollakPartialParking

/--
[pollak_partial_parking_functions_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean)
-/
@[path]
private lemma pollak_partial_parking_functions_card_eq
  {s t : ℕ}
-- given
  (hs : 0 < s)
  (hst : s ≤ t) :
-- imply
  Nat.card {f : Fin s → Fin t // IsPartialParkingFunction s t f} =
    (t + 1 - s) * (t + 1) ^ (s - 1) := by
-- proof
  apply MetaMathlibExt.PollakPartialParking.pollak_partial_parking_functions_card s t hs hst


-- created on 2026-10-20
-- updated on 2026-10-26
