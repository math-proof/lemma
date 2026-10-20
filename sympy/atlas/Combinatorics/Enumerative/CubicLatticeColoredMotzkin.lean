/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import sympy.atlas.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace MetaMathlibExt

/-- Flat color index for a non-distinguished cubic-lattice step. -/
private def flatIndex (n : ℕ) (x : Fin (n + 1) × Bool) (h : ¬x.1 = Fin.last n) :
    Fin (2 * n) :=
  ⟨x.1.val * 2 + (if x.2 then 1 else 0), by
    have hlt : x.1.val < n + 1 := x.1.isLt
    have hne : x.1.val ≠ n := by
      intro he
      apply h
      rw [Fin.ext_iff, Fin.val_last]
      exact he
    have hb : (if x.2 then (1 : ℕ) else 0) ≤ 1 := by
      cases x.2
      · simp
      · simp
    have hv : x.1.val < n := by omega
    omega⟩

/-- Value of the flat color index. -/
private theorem flatIndex_val (n : ℕ) (x : Fin (n + 1) × Bool)
    (h : ¬x.1 = Fin.last n) :
    (flatIndex n x h).val = x.1.val * 2 + (if x.2 then 1 else 0) := rfl

/-- Forward step map of the label bijection. -/
private def cubeToMotzkinStep (n : ℕ) (x : Fin (n + 1) × Bool) :
    Sum Bool (Fin (2 * n)) :=
  if h : x.1 = Fin.last n then Sum.inl x.2 else Sum.inr (flatIndex n x h)

/-- Backward step map. -/
private def motzkinToCubeStep (n : ℕ) (y : Sum Bool (Fin (2 * n))) :
    Fin (n + 1) × Bool :=
  Sum.elim (fun b => (Fin.last n, b)) (fun j =>
    (⟨j.val / 2, by
      have hj := j.isLt
      omega⟩, decide (j.val % 2 = 1))) y

/-- Forward map on a distinguished-coordinate step. -/
private theorem cubeToMotzkinStep_of_eq (n : ℕ) (x : Fin (n + 1) × Bool)
    (h : x.1 = Fin.last n) : cubeToMotzkinStep n x = Sum.inl x.2 := by
  simp [cubeToMotzkinStep, h]

/-- Forward map on a flat step. -/
private theorem cubeToMotzkinStep_of_ne (n : ℕ) (x : Fin (n + 1) × Bool)
    (h : ¬x.1 = Fin.last n) :
    cubeToMotzkinStep n x = Sum.inr (flatIndex n x h) := by
  simp [cubeToMotzkinStep, h]

/-- Encoding then decoding a flat index is the identity. -/
private theorem div2_encode (a : ℕ) (b : Bool) :
    (a * 2 + (if b then 1 else 0)) / 2 = a ∧
    decide ((a * 2 + (if b then 1 else 0)) % 2 = 1) = b := by
  cases b
  · exact ⟨by simp, by simp⟩
  · constructor
    · simp
      omega
    · simp

/-- Decoding then encoding a flat color is the identity. -/
private theorem mod2_decode (j : ℕ) :
    j / 2 * 2 + (if decide (j % 2 = 1) then 1 else 0) = j := by
  have hite : (if decide (j % 2 = 1) then (1 : ℕ) else 0) = j % 2 := by
    by_cases hc : j % 2 = 1
    · simp [hc]
    · have h0 : j % 2 = 0 := by omega
      simp [h0]
  rw [hite]
  omega

/-- The step maps preserve the weight. -/
private theorem step_weight (n : ℕ) (x : Fin (n + 1) × Bool) :
    Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
          (fun _ : Fin (2 * n) => (0 : ℤ)) (cubeToMotzkinStep n x) =
      (if x.1 = Fin.last n then (if x.2 = true then (1 : ℤ) else -1) else 0) := by
  unfold cubeToMotzkinStep
  by_cases h : x.1 = Fin.last n
  · simp [Sum.elim_inl, h]
  · simp [Sum.elim_inr, h]

/-- Backward map is a left inverse of the forward map. -/
private theorem step_left_inv (n : ℕ) (x : Fin (n + 1) × Bool) :
    motzkinToCubeStep n (cubeToMotzkinStep n x) = x := by
  by_cases h : x.1 = Fin.last n
  · rw [cubeToMotzkinStep_of_eq n x h]
    simp only [motzkinToCubeStep, Sum.elim_inl]
    exact Prod.ext h.symm rfl
  · rw [cubeToMotzkinStep_of_ne n x h]
    change ((⟨(flatIndex n x h).val / 2, by
      have hj := (flatIndex n x h).isLt
      omega⟩, decide ((flatIndex n x h).val % 2 = 1)) : Fin (n + 1) × Bool) = x
    obtain ⟨hd, hdec⟩ := div2_encode x.1.val x.2
    refine Prod.ext (Fin.ext_iff.mpr ?_) ?_
    · exact hd
    · exact hdec

/-- Forward map is a left inverse of the backward map. -/
private theorem step_right_inv (n : ℕ) (y : Sum Bool (Fin (2 * n))) :
    cubeToMotzkinStep n (motzkinToCubeStep n y) = y := by
  cases y with
  | inl b =>
    simp only [motzkinToCubeStep, Sum.elim_inl]
    exact cubeToMotzkinStep_of_eq n _ rfl
  | inr j =>
    by_cases h : (motzkinToCubeStep n (Sum.inr j)).1 = Fin.last n
    · have hcon := congrArg Fin.val h
      rw [Fin.val_last] at hcon
      have hcon2 : j.val / 2 = n := hcon
      have hj2 : j.val / 2 < n := by
        have hj := j.isLt
        omega
      have hfalse : False := by omega
      exact False.elim hfalse
    · rw [cubeToMotzkinStep_of_ne n (motzkinToCubeStep n (Sum.inr j)) h]
      congr 1
      rw [Fin.ext_iff, flatIndex_val]
      have hval : (motzkinToCubeStep n (Sum.inr j)).1.val = j.val / 2 := rfl
      have hval2 : (motzkinToCubeStep n (Sum.inr j)).2 = decide (j.val % 2 = 1) :=
        rfl
      rw [hval, hval2]
      exact mod2_decode j

/-- Pointwise equivalence of steps. -/
private def stepEquiv (n : ℕ) : (Fin (n + 1) × Bool) ≃ Sum Bool (Fin (2 * n)) :=
  ⟨cubeToMotzkinStep n, motzkinToCubeStep n, step_left_inv n, step_right_inv n⟩

/-- Colored Motzkin steps as `(u,l,d)`-Motzkin steps of rank `1` with one up color, `2 * n`
level colors, and one down color. -/
private def motzkinStepEquiv (n : ℕ) :
    Sum Bool (Fin (2 * n)) ≃ ULDMotzkin.ULDMotzkinStep 1 (fun _ => 1) (2 * n) (fun _ => 1) where
  toFun := Sum.elim (fun b => if b then Sum.inl ⟨0, 0⟩ else Sum.inr (Sum.inr ⟨0, 0⟩))
    (fun j => Sum.inr (Sum.inl j))
  invFun s := match s with
    | Sum.inl _ => Sum.inl true
    | Sum.inr (Sum.inl j) => Sum.inr j
    | Sum.inr (Sum.inr _) => Sum.inl false
  left_inv y := by
    rcases y with (_ | _) | _ <;> rfl
  right_inv s := by
    rcases s with ⟨j, c⟩ | j | ⟨j, c⟩
    · obtain rfl := Subsingleton.elim j 0
      obtain rfl := Subsingleton.elim c 0
      rfl
    · rfl
    · obtain rfl := Subsingleton.elim j 0
      obtain rfl := Subsingleton.elim c 0
      rfl

/-- `motzkinStepEquiv` preserves the height of a step. -/
private theorem stepHeight_motzkinStepEquiv (n : ℕ) (y : Sum Bool (Fin (2 * n))) :
    ULDMotzkin.stepHeight 1 (fun _ => 1) (2 * n) (fun _ => 1) (motzkinStepEquiv n y) =
      Sum.elim (fun b : Bool => if b = true then (1 : ℤ) else -1)
        (fun _ : Fin (2 * n) => (0 : ℤ)) y := by
  rcases y with (_ | _) | _ <;> simp [motzkinStepEquiv, ULDMotzkin.stepHeight]

/-- Paths of `k` steps in `α` whose weights have nonnegative prefix sums and total zero are
counted by `uldMotzkinNumber`, given a height-preserving equivalence of steps. -/
private theorem card_eq_uldMotzkinNumber {α : Type*} [Fintype α] (n k : ℕ) (w : α → ℤ)
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

/-- Colored Motzkin paths with one up color, `2 * n` level colors, and one down color, encoded
as step sequences in `Sum Bool (Fin (2 * n))`, are counted by `uldMotzkinNumber`. -/
private theorem colored_motzkin_card_eq_uldMotzkinNumber (n k : ℕ) :
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

/--
Lattice paths in the cubic lattice of dimension `n + 1` of length `k`, with the last
coordinate constrained to a Dyck bridge, are counted by the `(u,l,d)`-Motzkin number of
rank `1` with one up color, `2 * n` level colors, and one down color.

Source: Rigoberto Flórez, Leandro Junes, and José L. Ramírez, "Further
Results on Paths in an n-Dimensional Cubic Lattice," Journal of Integer
Sequences 21 (2018), Article 18.1.2, Theorem (label bijection:Motzkin),
lines 924–926,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.tex
-/
theorem cube_lattice_paths_card_eq_uldMotzkinNumber (n k : ℕ) :
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
  have h := card_eq_uldMotzkinNumber n k
    (fun x : Fin (n + 1) × Bool =>
      if x.1 = Fin.last n then (if x.2 = true then (1 : ℤ) else -1) else 0)
    ((stepEquiv n).trans (motzkinStepEquiv n)) fun x => by
      rw [Equiv.trans_apply, stepHeight_motzkinStepEquiv]
      exact step_weight n x
  beta_reduce at h
  exact h

/--
Lattice paths in the cubic lattice and colored Motzkin paths.

Source: Rigoberto Flórez, Leandro Junes, and José L. Ramírez, "Further
Results on Paths in an n-Dimensional Cubic Lattice," Journal of Integer
Sequences 21 (2018), Article 18.1.2, Theorem (label bijection:Motzkin),
lines 924–926,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.tex

The formalization is the paper's theorem at dimension `n + 1`: both sides
use `2 * n` flat-step colors, and only the distinguished coordinate is
constrained to a Dyck bridge. Both sides equal
`ULDMotzkin.uldMotzkinNumber 1 (fun _ => 1) (2 * n) (fun _ => 1) le_rfl k`; see
`cube_lattice_paths_card_eq_uldMotzkinNumber`.

Proves `Wanted` entry `cube_lattice_paths_card_eq_colored_motzkin_card`.
-/
theorem cube_lattice_paths_card_eq_colored_motzkin_card (n k : ℕ) :
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
  rw [cube_lattice_paths_card_eq_uldMotzkinNumber, colored_motzkin_card_eq_uldMotzkinNumber]

end MetaMathlibExt
