import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.CubicLatticeColoredMotzkin.Part3
open MetaMathlibExt


namespace MetaMathlibExt

/--
[step_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
private lemma step_weight (n : ℕ) (x : Fin (n + 1) × Bool) :
  Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
    (fun _ : Fin (2 * n) => (0 : ℤ)) (cubeToMotzkinStep n x) =
    (if x.1 = Fin.last n then (if x.2 = true then (1 : ℤ) else -1) else 0) := by
  unfold cubeToMotzkinStep
  by_cases h : x.1 = Fin.last n
  · simp [Sum.elim_inl, h]
  · simp [Sum.elim_inr, h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stepHeight_motzkinStepEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
private lemma stepHeight_motzkinStepEquiv (n : ℕ) (y : Sum Bool (Fin (2 * n))) :
  ULDMotzkin.stepHeight 1 (fun _ => 1) (2 * n) (fun _ => 1) (motzkinStepEquiv n y) =
    Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
      (fun _ : Fin (2 * n) => (0 : ℤ)) y := by
  obtain (_ | _) | _ <;> simp [motzkinStepEquiv, ULDMotzkin.stepHeight] := y

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_eq_uldMotzkinNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
counted by `uldMotzkinNumber`, given a height-preserving equivalence of steps. -/
private lemma card_eq_uldMotzkinNumber {α : Type*} [Fintype α] (n k : ℕ) (w : α → ℤ)
  (e : α ≃ ULDMotzkin.ULDMotzkinStep 1 (fun _ => 1) (2 * n) (fun _ => 1))
  (he : ∀ a, ULDMotzkin.stepHeight 1 (fun _ => 1) (2 * n) (fun _ => 1) (e a) = w a) :
  Fintype.card { p : Fin k → α //
    (∀ t : Fin (k + 1), 0 ≤ ∑ i : Fin t.val, w (p (Fin.castLE (Nat.le_of_lt_succ t.isLt) i))) ∧
    ∑ i : Fin k, w (p i) = 0 } =
  ULDMotzkin.uldMotzkinNumber 1 (fun _ => 1) (2 * n) (fun _ => 1) le_rfl k := by
  rw [ULDMotzkin.uldMotzkinNumber_eq_card]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => e) fun p => ?_)
  have hpre : ∀ (m : ℕ) (hm : m ≤ k), ∑ i : Fin m, w (p (Fin.castLE hm i)) =
    ULDMotzkin.pathHeight 1 (fun _ => 1) (2 * n) (fun _ => 1) k
      (Equiv.piCongrRight (fun _ => e) p) m := by
    intro m hm
    rw [ULDMotzkin.pathHeight, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dite_eq_left (lt_of_lt_of_le i.isLt hm), ← he]
    rfl
  have htot : ∑ i : Fin k, w (p i) =
    ULDMotzkin.pathHeight 1 (fun _ => 1) (2 * n) (fun _ => 1) k
      (Equiv.piCongrRight (fun _ => e) p) k :=
    hpre k le_rfl
  rw [ULDMotzkin.IsMotzkinPath, ← htot]
  refine and_congr ⟨fun h m hm => ?_, fun h t => ?_⟩ Iff.rfl
  · have hm' := Finset.mem_range.mp hm
    rw [← hpre m (by omega)]
    exact h ⟨m, hm'⟩
  · rw [hpre]
    exact h t (Finset.mem_range.mpr t.isLt)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[colored_motzkin_card_eq_uldMotzkinNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
as step sequences in `Sum Bool (Fin (2 * n))`, are counted by `uldMotzkinNumber`. -/
private lemma colored_motzkin_card_eq_uldMotzkinNumber (n k : ℕ) :
  Fintype.card { q : Fin k → Sum Bool (Fin (2 * n)) //
    (∀ t : Fin (k + 1), 0 ≤ ∑ i : Fin t.val,
      Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
        (fun _ : Fin (2 * n) => (0 : ℤ))
        (q (Fin.castLE (Nat.le_of_lt_succ t.isLt) i))) ∧
    ∑ i : Fin k,
      Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
        (fun _ : Fin (2 * n) => (0 : ℤ)) (q i) = 0 } =
  ULDMotzkin.uldMotzkinNumber 1 (fun _ => 1) (2 * n) (fun _ => 1) le_rfl k :=
  card_eq_uldMotzkinNumber n k _ (motzkinStepEquiv n) (stepHeight_motzkinStepEquiv n)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cube_lattice_paths_card_eq_uldMotzkinNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
lemma cube_lattice_paths_card_eq_uldMotzkinNumber
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
  have h := card_eq_uldMotzkinNumber n k
    (fun x : Fin (n + 1) × Bool =>
      if x.1 = Fin.last n then (if x.2 = true then (1 : ℤ) else -1) else 0)
    ((stepEquiv n).trans (motzkinStepEquiv n)) fun x => by
      rw [Equiv.trans_apply, stepHeight_motzkinStepEquiv]
      exact step_weight n x
  beta_reduce at h
  exact h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cube_lattice_paths_card_eq_colored_motzkin_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean)
-/
@[path]
lemma cube_lattice_paths_card_eq_colored_motzkin_card
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
  rw [cube_lattice_paths_card_eq_uldMotzkinNumber, colored_motzkin_card_eq_uldMotzkinNumber]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
