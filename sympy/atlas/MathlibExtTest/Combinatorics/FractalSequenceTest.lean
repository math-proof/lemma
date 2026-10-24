/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import sympy.atlas.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic

namespace MetaMathlibExt

example (X : FractalSequence) (n : ℕ) (h : X.seq n = 0 + 2) :
    ∃ m, m < n ∧ X.seq m = 0 + 1 :=
  X.cond_F2 n 0 h

example (X : FractalSequence) : X.seq (X.pos 0 0) = 0 + 1 :=
  X.pos_sound 0 0

example (X : FractalSequence) (j : ℕ) :
    ∃! k, X.pos 1 j < X.pos 0 k ∧ X.pos 0 k < X.pos 1 (j + 1) :=
  X.cond_F3 0 1 j (by decide)

example (X : FractalSequence) (j k₁ k₂ : ℕ)
    (h₁ : X.pos 1 j < X.pos 0 k₁ ∧ X.pos 0 k₁ < X.pos 1 (j + 1))
    (h₂ : X.pos 1 j < X.pos 0 k₂ ∧ X.pos 0 k₂ < X.pos 1 (j + 1)) :
    k₁ = k₂ := by
  obtain ⟨k, _, huniq⟩ := X.cond_F3 0 1 j (by decide)
  have e₁ := huniq k₁ h₁
  have e₂ := huniq k₂ h₂
  rw [e₁, e₂]

example (X : FractalSequence) : 0 < X.seq 0 :=
  X.seq_pos 0

example (X : FractalSequence) (i : ℕ) : X.pos i 0 < X.pos (i + 1) 0 :=
  X.pos_column_strict 0 (Nat.lt_succ_self i)

/-! ### A concrete regular fractal sequence

The following realizes A002260, Example 5 in the source: concatenate the finite blocks
`(1)`, `(1, 2)`, `(1, 2, 3)`, and so on.  The zero-based position of the `j`th occurrence
of `i + 1` is `triangle (i + j) + i`.
-/

private def triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangle n + n + 1

@[simp] private theorem triangle_zero : triangle 0 = 0 := rfl

@[simp] private theorem triangle_succ (n : ℕ) :
    triangle (n + 1) = triangle n + n + 1 := rfl

private def diagPos (i j : ℕ) : ℕ := triangle (i + j) + i

private theorem diagPos_strict_right (i : ℕ) : StrictMono (diagPos i) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [diagPos]
  rw [show i + (j + 1) = (i + j) + 1 by omega, triangle_succ]
  omega

private theorem diagPos_strict_left (j : ℕ) : StrictMono (fun i => diagPos i j) := by
  apply strictMono_nat_of_lt_succ
  intro i
  simp only [diagPos]
  rw [show i + 1 + j = (i + j) + 1 by omega, triangle_succ]
  omega

private theorem diagPos_injective : Function.Injective (Function.uncurry diagPos) := by
  rintro ⟨i, j⟩ ⟨h, k⟩ heq
  change diagPos i j = diagPos h k at heq
  have hij_lo : triangle (i + j) ≤ diagPos i j := by simp [diagPos]
  have hij_hi : diagPos i j < triangle (i + j + 1) := by
    simp only [diagPos, triangle_succ]
    omega
  have hhk_lo : triangle (h + k) ≤ diagPos h k := by simp [diagPos]
  have hhk_hi : diagPos h k < triangle (h + k + 1) := by
    simp only [diagPos, triangle_succ]
    omega
  have hsum : i + j = h + k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : triangle (i + j + 1) ≤ triangle (h + k) :=
        triangle_strict.monotone (by omega)
      omega
    · have hstep : triangle (h + k + 1) ≤ triangle (i + j) :=
        triangle_strict.monotone (by omega)
      omega
  have hi : i = h := by
    unfold diagPos at heq
    rw [hsum] at heq
    omega
  exact Prod.ext hi (by omega)

private def diagUnpair : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let p := diagUnpair n
      if p.2 = 0 then (0, p.1 + 1) else (p.1 + 1, p.2 - 1)

private theorem diagPos_diagUnpair (n : ℕ) :
    diagPos (diagUnpair n).1 (diagUnpair n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [diagUnpair]
    split_ifs with hj
    · have ih' : triangle (diagUnpair n).1 + (diagUnpair n).1 = n := by
        simpa [diagPos, hj] using ih
      simp only [diagPos, zero_add]
      rw [triangle_succ]
      omega
    · have ih' : triangle ((diagUnpair n).1 + (diagUnpair n).2) +
          (diagUnpair n).1 = n := by simpa [diagPos] using ih
      simp only [diagPos]
      have hjpos : 0 < (diagUnpair n).2 := Nat.pos_of_ne_zero hj
      rw [show (diagUnpair n).1 + 1 + ((diagUnpair n).2 - 1) =
        (diagUnpair n).1 + (diagUnpair n).2 by omega]
      omega

private theorem diagUnpair_diagPos (i j : ℕ) : diagUnpair (diagPos i j) = (i, j) := by
  apply diagPos_injective
  change diagPos (diagUnpair (diagPos i j)).1 (diagUnpair (diagPos i j)).2 = diagPos i j
  exact diagPos_diagUnpair (diagPos i j)

private def diagonalSequence (n : ℕ) : ℕ := (diagUnpair n).1 + 1

private def diagonalFractal : FractalSequence where
  seq := diagonalSequence
  seq_pos := by intro n; simp [diagonalSequence]
  pos := diagPos
  pos_strict := diagPos_strict_right
  pos_sound := by intro i j; simp [diagonalSequence, diagUnpair_diagPos]
  pos_complete := by
    intro i n h
    refine ⟨(diagUnpair n).2, ?_⟩
    have hi : (diagUnpair n).1 = i := by simpa [diagonalSequence] using h
    rw [← hi, diagPos_diagUnpair]
  cond_F2 := by
    intro n i h
    let u := diagUnpair n
    have hu : u.1 = i + 1 := by simpa [u, diagonalSequence] using h
    have hn : diagPos u.1 u.2 = n := by simpa [u] using diagPos_diagUnpair n
    refine ⟨diagPos i u.2, ?_, ?_⟩
    · rw [← hn, hu]
      exact diagPos_strict_left u.2 (Nat.lt_succ_self i)
    · simp [diagonalSequence, diagUnpair_diagPos]
  cond_F3 := by
    intro h i j hhi
    let k := j + i - h + 1
    refine ⟨k, ?_, ?_⟩
    · dsimp only [k]
      simp only [diagPos]
      rw [show h + (j + i - h + 1) = (i + j) + 1 by omega, triangle_succ]
      rw [show i + (j + 1) = (i + j) + 1 by omega, triangle_succ]
      omega
    · intro l hl
      have hkpos : 0 < k := by simp [k]
      have hprev : diagPos h (k - 1) ≤ diagPos i j := by
        simp only [diagPos]
        rw [show h + (k - 1) = i + j by dsimp only [k]; omega]
        omega
      have hnext : diagPos i (j + 1) ≤ diagPos h (k + 1) := by
        change triangle (i + (j + 1)) + i ≤ triangle (h + (k + 1)) + h
        rw [show i + (j + 1) = (i + j) + 1 by omega,
          show h + (k + 1) = ((i + j) + 1) + 1 by dsimp only [k]; omega]
        rw [triangle_succ ((i + j) + 1), triangle_succ (i + j)]
        omega
      have hkl : k ≤ l := by
        by_contra hnot
        have hle : l ≤ k - 1 := by omega
        have := (diagPos_strict_right h).monotone hle
        omega
      have hlk : l ≤ k := by
        by_contra hnot
        have hle : k + 1 ≤ l := by omega
        have := (diagPos_strict_right h).monotone hle
        omega
      omega
  pos_column_strict := diagPos_strict_left

example : diagonalFractal.seq 0 = 1 := rfl
example : diagonalFractal.seq 1 = 1 := rfl
example : diagonalFractal.seq 2 = 2 := rfl
example : diagonalFractal.seq 5 = 3 := rfl
example : diagonalFractal.pos 2 1 = 8 := rfl

end MetaMathlibExt
