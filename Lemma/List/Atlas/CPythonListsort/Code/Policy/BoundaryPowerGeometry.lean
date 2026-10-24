import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Policy.BoundaryPowerGeometry
open CPythonListsort


namespace CPythonListsort

/--
[ofNat64_toNat_of_le_pyListMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
by the selected 64-bit `Py_ssize_t` model. -/
private lemma ofNat64_toNat_of_le_pyListMax {x : Nat}
  (hx : x ≤ PY_LIST_MAX) :
  (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [pyListMax_eq] at hx
  norm_num at hx ⊢
  omega

end CPythonListsort

namespace CPythonListsort

/--
[ofNat64_nonnegative_of_le_pyListMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
exact `BitVec.ofNat 64` conversion. -/
private lemma ofNat64_nonnegative_of_le_pyListMax {x : Nat}
  (hx : x ≤ PY_LIST_MAX) :
  PySSize.Nonnegative (BitVec.ofNat 64 x) := by
  rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
  rw [ofNat64_toNat_of_le_pyListMax hx]
  rw [pyListMax_eq] at hx
  norm_num at hx ⊢
  omega

end CPythonListsort

namespace CPythonListsort

/--
[validPowerloopInput_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
lemma validPowerloopInput_ofNat
  {s u v n : Nat}
-- given
  (hu : 0 < u)
  (hv : 0 < v)
  (hfits : s + u + v ≤ n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ValidPowerloopInput (BitVec.ofNat 64 s) (BitVec.ofNat 64 u) (BitVec.ofNat 64 v) (BitVec.ofNat 64 n) := by
-- proof
  have hs : s ≤ PY_LIST_MAX := by omega
  have huMax : u ≤ PY_LIST_MAX := by omega
  have hvMax : v ≤ PY_LIST_MAX := by omega
  refine ⟨ofNat64_nonnegative_of_le_pyListMax hs,
    ofNat64_nonnegative_of_le_pyListMax huMax,
    ofNat64_nonnegative_of_le_pyListMax hvMax,
    ofNat64_nonnegative_of_le_pyListMax hnmax, ?_, ?_, ?_, ?_⟩
  · rwa [ofNat64_toNat_of_le_pyListMax huMax]
  · rwa [ofNat64_toNat_of_le_pyListMax hvMax]
  · rw [ofNat64_toNat_of_le_pyListMax hs,
    ofNat64_toNat_of_le_pyListMax huMax,
    ofNat64_toNat_of_le_pyListMax hvMax,
    ofNat64_toNat_of_le_pyListMax hnmax]
    exact hfits
  · rwa [ofNat64_toNat_of_le_pyListMax hnmax]

end CPythonListsort

namespace CPythonListsort

/--
[scaledQuotient_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
private lemma scaledQuotient_mod_two (x n k : Nat) :
  scaledQuotient x n k % 2 = powerloopQuotientBit x n k := by
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[scaledQuotient_succ_div_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
scaled quotient. -/
private lemma scaledQuotient_succ_div_two (x n k : Nat) :
  scaledQuotient x n (k + 1) / 2 = scaledQuotient x n k := by
  unfold scaledQuotient
  rw [Nat.div_div_eq_div_mul]
  rw [pow_succ]
  have htwo : 0 < (2 : Nat) := by omega
  calc
    2 ^ k * 2 * x / (n * 2) = 2 * (2 ^ k * x) / (2 * n) := by
      congr 1 <;> ring
    _ = 2 ^ k * x / n := Nat.mul_div_mul_left (2 ^ k * x) n htwo

end CPythonListsort

namespace CPythonListsort

/--
[scaledQuotient_eq_of_bits_eq_up_to](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
through depth `k` is equivalent to agreement of the whole scaled quotient at
that depth.  Only the forward direction is needed below. -/
private lemma scaledQuotient_eq_of_bits_eq_up_to
  {x y n k : Nat} (hx : x < 2 * n) (hy : y < 2 * n)
  (hbits : ∀ j ≤ k,
    powerloopQuotientBit x n j = powerloopQuotientBit y n j) :
  scaledQuotient x n k = scaledQuotient y n k := by
  induction k with
  | zero =>
    have hn : 0 < n := by omega
    have hxq : scaledQuotient x n 0 < 2 := by
      simpa [scaledQuotient] using (Nat.div_lt_iff_lt_mul hn).2 hx
    have hyq : scaledQuotient y n 0 < 2 := by
      simpa [scaledQuotient] using (Nat.div_lt_iff_lt_mul hn).2 hy
    have hmod : scaledQuotient x n 0 % 2 = scaledQuotient y n 0 % 2 :=
      (scaledQuotient_mod_two x n 0).trans
        ((hbits 0 (by omega)).trans (scaledQuotient_mod_two y n 0).symm)
    rwa [Nat.mod_eq_of_lt hxq, Nat.mod_eq_of_lt hyq] at hmod
  | succ k ih =>
    have hprior : ∀ j ≤ k,
      powerloopQuotientBit x n j = powerloopQuotientBit y n j := by
      intro j hj
      exact hbits j (by omega)
    have hdiv :
      scaledQuotient x n (k + 1) / 2 =
        scaledQuotient y n (k + 1) / 2 := by
      rw [scaledQuotient_succ_div_two, scaledQuotient_succ_div_two]
      exact ih hprior
    have hmod :
      scaledQuotient x n (k + 1) % 2 =
        scaledQuotient y n (k + 1) % 2 := by
      rw [scaledQuotient_mod_two, scaledQuotient_mod_two]
      exact hbits (k + 1) (by omega)
    have hxsplit := Nat.mod_add_div (scaledQuotient x n (k + 1)) 2
    have hysplit := Nat.mod_add_div (scaledQuotient y n (k + 1)) 2
    omega

end CPythonListsort

namespace CPythonListsort

/--
[quotientBits_eq_of_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
that same prefix.  This is the dyadic-cell convexity fact used by both
absorption laws. -/
private lemma quotientBits_eq_of_between
  {x q z n k : Nat} (hxq : x ≤ q) (hqz : q ≤ z)
  (hx : x < 2 * n) (hz : z < 2 * n)
  (hbits : ∀ j ≤ k,
    powerloopQuotientBit x n j = powerloopQuotientBit z n j) :
  ∀ j ≤ k, powerloopQuotientBit x n j = powerloopQuotientBit q n j := by
  intro j hj
  have hprefix : scaledQuotient x n j = scaledQuotient z n j :=
    scaledQuotient_eq_of_bits_eq_up_to hx hz (fun i hi => hbits i (le_trans hi hj))
  have hleft : scaledQuotient x n j ≤ scaledQuotient q n j := by
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left (2 ^ j) hxq
  have hright : scaledQuotient q n j ≤ scaledQuotient z n j := by
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left (2 ^ j) hqz
  have hscaled : scaledQuotient x n j = scaledQuotient q n j := by omega
  rw [← scaledQuotient_mod_two, ← scaledQuotient_mod_two, hscaled]

end CPythonListsort

namespace CPythonListsort

/--
[firstDifferingQuotientBit_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
private lemma firstDifferingQuotientBit_unique
  {x y n k l : Nat}
  (hk : IsFirstDifferingQuotientBit x y n k)
  (hl : IsFirstDifferingQuotientBit x y n l) :
  k = l := by
  obtain ⟨hxk, hyk, hpriorK⟩ := hk
  obtain ⟨hxl, hyl, hpriorL⟩ := hl
  by_contra hne
  obtain hkl | hlk := lt_or_gt_of_ne hne
  · have := hpriorL k hkl
    omega
  · have := hpriorK l hlk
    omega

end CPythonListsort

namespace CPythonListsort

/--
[boundaryPowerGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean)
-/
@[path]
lemma boundaryPowerGeometry
  {s a b c n : Nat}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hfits : s + a + b + c ≤ n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  let P := fun x u v : Nat => powerloop (BitVec.ofNat 64 x) (BitVec.ofNat 64 u) (BitVec.ofNat 64 v) (BitVec.ofNat 64 n) let pAB := P s a b let pBC := P (s + a) b c pAB ≠ pBC ∧ (pAB < pBC → P s a (b + c) = pAB) ∧ (pBC < pAB → P s (a + b) c = pBC) := by
-- proof
  dsimp only
  have hn : 0 < n := by omega
  have hs : s ≤ PY_LIST_MAX := by omega
  have haMax : a ≤ PY_LIST_MAX := by omega
  have hbMax : b ≤ PY_LIST_MAX := by omega
  have hcMax : c ≤ PY_LIST_MAX := by omega
  have hsaMax : s + a ≤ PY_LIST_MAX := by omega
  have habMax : a + b ≤ PY_LIST_MAX := by omega
  have hbcMax : b + c ≤ PY_LIST_MAX := by omega
  have hnNat : (BitVec.ofNat 64 n).toNat = n :=
    ofNat64_toNat_of_le_pyListMax hnmax
  have hABValid := validPowerloopInput_ofNat (s := s) (n := n) ha hb (by omega) hnmax
  have hBCValid := validPowerloopInput_ofNat (s := s + a) (n := n) hb hc
    (by omega : (s + a) + b + c ≤ n) hnmax
  have hRightValid := validPowerloopInput_ofNat (s := s) (n := n)
    ha (by omega : 0 < b + c)
    (by omega : s + a + (b + c) ≤ n) hnmax
  have hLeftValid := validPowerloopInput_ofNat (s := s) (n := n)
    (by omega : 0 < a + b) hc
    (by omega : s + (a + b) + c ≤ n) hnmax
  have hABResult := powerloopResult
    (BitVec.ofNat 64 s) (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
    (BitVec.ofNat 64 n) hABValid
  have hBCResult := powerloopResult
    (BitVec.ofNat 64 (s + a)) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c)
    (BitVec.ofNat 64 n) hBCValid
  have hRightResult := powerloopResult
    (BitVec.ofNat 64 s) (BitVec.ofNat 64 a) (BitVec.ofNat 64 (b + c))
    (BitVec.ofNat 64 n) hRightValid
  have hLeftResult := powerloopResult
    (BitVec.ofNat 64 s) (BitVec.ofNat 64 (a + b)) (BitVec.ofNat 64 c)
    (BitVec.ofNat 64 n) hLeftValid
  simp only [ofNat64_toNat_of_le_pyListMax hs,
    ofNat64_toNat_of_le_pyListMax haMax,
    ofNat64_toNat_of_le_pyListMax hbMax, hnNat] at hABResult
  simp only [ofNat64_toNat_of_le_pyListMax hsaMax,
    ofNat64_toNat_of_le_pyListMax hbMax,
    ofNat64_toNat_of_le_pyListMax hcMax, hnNat] at hBCResult
  simp only [ofNat64_toNat_of_le_pyListMax hs,
    ofNat64_toNat_of_le_pyListMax haMax,
    ofNat64_toNat_of_le_pyListMax hbcMax, hnNat] at hRightResult
  simp only [ofNat64_toNat_of_le_pyListMax hs,
    ofNat64_toNat_of_le_pyListMax habMax,
    ofNat64_toNat_of_le_pyListMax hcMax, hnNat] at hLeftResult
  obtain ⟨_, kAB, _, hpAB, hkAB⟩ := hABResult
  obtain ⟨_, kBC, _, hpBC, hkBC⟩ := hBCResult
  obtain ⟨_, kRight, _, hpRight, hkRight⟩ := hRightResult
  obtain ⟨_, kLeft, _, hpLeft, hkLeft⟩ := hLeftResult
  let x := 2 * s + a
  let m := 2 * s + a + a + b
  let z := 2 * (s + a) + b + b + c
  let qRight := 2 * s + a + a + (b + c)
  let qLeft := 2 * s + (a + b)
  have hx : x < 2 * n := by dsimp [x]; omega
  have hm : m < 2 * n := by dsimp [m]; omega
  have hz : z < 2 * n := by dsimp [z]; omega
  have hxm : x < m := by dsimp [x, m]; omega
  have hmz : m < z := by dsimp [m, z]; omega
  have hmqRight : m ≤ qRight := by dsimp [m, qRight]; omega
  have hqRightz : qRight ≤ z := by dsimp [qRight, z]; omega
  have hxqLeft : x ≤ qLeft := by dsimp [x, qLeft]; omega
  have hqLeftm : qLeft ≤ m := by dsimp [qLeft, m]; omega
  have hkAB' : IsFirstDifferingQuotientBit x m n kAB := hkAB
  have hkBC' : IsFirstDifferingQuotientBit m z n kBC := by
    have hmBC : m = 2 * (s + a) + b := by
      dsimp [m]
      omega
    rwa [hmBC]
  have hkRight' : IsFirstDifferingQuotientBit x qRight n kRight := hkRight
  have hkLeft' : IsFirstDifferingQuotientBit qLeft z n kLeft := by
    have hzLeft : z = 2 * s + (a + b) + (a + b) + c := by
      dsimp [z]
      omega
    rwa [hzLeft]
  have hpNe :
    powerloop (BitVec.ofNat 64 s) (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
      (BitVec.ofNat 64 n) ≠
      powerloop (BitVec.ofNat 64 (s + a)) (BitVec.ofNat 64 b)
        (BitVec.ofNat 64 c) (BitVec.ofNat 64 n) := by
    intro heq
    have hkEq : kAB = kBC := by omega
    subst kBC
    exact Nat.zero_ne_one (hkBC'.1.symm.trans hkAB'.2.1)
  refine ⟨hpNe, ?_, ?_⟩
  · intro hpLt
    have hkLt : kAB < kBC := by omega
    have hmzBits : ∀ j ≤ kAB,
      powerloopQuotientBit m n j = powerloopQuotientBit z n j := by
      intro j hj
      exact hkBC'.2.2 j (by omega)
    have hmRightBits : ∀ j ≤ kAB,
      powerloopQuotientBit m n j = powerloopQuotientBit qRight n j :=
      quotientBits_eq_of_between hmqRight hqRightz hm hz hmzBits
    have hkCandidate : IsFirstDifferingQuotientBit x qRight n kAB := by
      refine ⟨hkAB'.1, ?_, ?_⟩
      · exact (hmRightBits kAB (by omega)) ▸ hkAB'.2.1
      · intro j hj
        exact (hkAB'.2.2 j hj).trans (hmRightBits j (by omega))
    have hkSame : kRight = kAB :=
      firstDifferingQuotientBit_unique hkRight' hkCandidate
    omega
  · intro hpLt
    have hkLt : kBC < kAB := by omega
    have hxmBits : ∀ j ≤ kBC,
      powerloopQuotientBit x n j = powerloopQuotientBit m n j := by
      intro j hj
      exact hkAB'.2.2 j (by omega)
    have hxLeftBits : ∀ j ≤ kBC,
      powerloopQuotientBit x n j = powerloopQuotientBit qLeft n j :=
      quotientBits_eq_of_between hxqLeft hqLeftm hx hm hxmBits
    have hkCandidate : IsFirstDifferingQuotientBit qLeft z n kBC := by
      refine ⟨?_, hkBC'.2.1, ?_⟩
      · exact (hxLeftBits kBC (by omega)).symm.trans
        ((hxmBits kBC (by omega)).trans hkBC'.1)
      · intro j hj
        exact (hxLeftBits j (by omega)).symm.trans
          ((hxmBits j (by omega)).trans (hkBC'.2.2 j hj))
    have hkSame : kLeft = kBC :=
      firstDifferingQuotientBit_unique hkLeft' hkCandidate
    omega

end CPythonListsort


-- created on 2026-10-23
