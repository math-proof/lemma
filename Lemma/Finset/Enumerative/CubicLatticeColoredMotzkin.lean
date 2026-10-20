import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CubicLatticeColoredMotzkin
open MetaMathlibExt


/--
[cube_lattice_paths_card_eq_uldMotzkinNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
private lemma cube_lattice_paths_card_eq_uldMotzkinNumber_eq
  {n k : ℕ} :
-- imply
  Fintype.card { p : Fin k → Fin (n + 1) × Bool //
    (∀ t : Fin (k + 1), 0 ≤ ∑ i : Fin t.val,
    (if (p (Fin.castLE (Nat.le_of_lt_succ t.isLt) i)).1 = Fin.last n then
    (if (p (Fin.castLE (Nat.le_of_lt_succ t.isLt) i)).2 = true then (1 : ℤ) else -1)
    else 0)) ∧
    ∑ i : Fin k,
    (if (p i).1 = Fin.last n then
    (if (p i).2 = true then (1 : ℤ) else -1)
    else 0) = 0 } =
    ULDMotzkin.uldMotzkinNumber 1 (fun _ => 1) (2 * n) (fun _ => 1) le_rfl k := by
-- proof
  apply MetaMathlibExt.cube_lattice_paths_card_eq_uldMotzkinNumber n k

/--
[cube_lattice_paths_card_eq_colored_motzkin_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
private lemma cube_lattice_paths_card_eq_colored_motzkin_card_eq
  {n k : ℕ} :
-- imply
  Fintype.card { p : Fin k → Fin (n + 1) × Bool //
    (∀ t : Fin (k + 1), 0 ≤ ∑ i : Fin t.val,
    (if (p (Fin.castLE (Nat.le_of_lt_succ t.isLt) i)).1 = Fin.last n then
    (if (p (Fin.castLE (Nat.le_of_lt_succ t.isLt) i)).2 = true then (1 : ℤ) else -1)
    else 0)) ∧
    ∑ i : Fin k,
    (if (p i).1 = Fin.last n then
    (if (p i).2 = true then (1 : ℤ) else -1)
    else 0) = 0 } =
    Fintype.card { q : Fin k → Sum Bool (Fin (2 * n)) //
    (∀ t : Fin (k + 1), 0 ≤ ∑ i : Fin t.val,
    Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
    (fun _ : Fin (2 * n) => (0 : ℤ))
    (q (Fin.castLE (Nat.le_of_lt_succ t.isLt) i))) ∧
    ∑ i : Fin k,
    Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
    (fun _ : Fin (2 * n) => (0 : ℤ)) (q i) = 0 } := by
-- proof
  apply MetaMathlibExt.cube_lattice_paths_card_eq_colored_motzkin_card n k


-- created on 2026-10-20
