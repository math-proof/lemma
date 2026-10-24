import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.WorpitzkyMultisetIdentity
open MetaMathlibExt


namespace MetaMathlibExt

/--
[desInd_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean)
-/
@[path]
private lemma desInd_le_one {m K : ℕ} (w : Fin K → Fin m) (n : ℕ) :
  desInd w n ≤ 1 := by
  unfold desInd
  by_cases hn : n + 1 < K
  · simp only [hn, dite_true]
    by_cases hw : w ⟨n, by omega⟩ > w ⟨n + 1, hn⟩
    · simp only [hw, ite_true]
      omega
    · simp only [hw, ite_false]
      omega
  · simp only [hn, dite_false]
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[worpitzky_lhs_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean)
-/
@[path]
private lemma worpitzky_lhs_card (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
  Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
    Fintype.card (∀ i, Sym (Fin x) (k i)) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wmi_card_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean)
-/
@[path]
private lemma wmi_card_monotone (K y : ℕ) :
  Fintype.card { g : Fin K → Fin y // Monotone g } =
    Nat.choose (y + K - 1) K := by
  rw [Fintype.card_congr wmiMonoEquivSym, Sym.card_sym_eq_choose,
    Fintype.card_fin]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wmi_desInd_eq_ite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean)
-/
@[path]
private lemma wmi_desInd_eq_ite {m K : ℕ} (w : Fin K → Fin m)
  (j : Fin K) :
  desInd w j.val =
    if (∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩) then 1 else 0 := by
  unfold desInd
  by_cases h : j.val + 1 < K
  · simp only [h, dite_true]
    have hj : (⟨j.val, by omega⟩ : Fin K) = j := Fin.ext rfl
    rw [hj]
    by_cases hd : w j > w ⟨j.val + 1, h⟩
    · simp [hd]
    · simp [hd]
  · simp [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wmi_word_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean)
-/
@[path]
private lemma wmi_word_fiber_card (m : ℕ) (k : Fin m → ℕ) (p : ℕ) :
  Fintype.card { w : wmiWords m k // wmiDesClass w.1 = p } =
    Nat.card { w : Fin (∑ i, k i) → Fin m //
      (∀ i, Fintype.card { j : Fin (∑ i, k i) // w j = i } = k i) ∧
      (Finset.univ.filter (fun j : Fin (∑ i, k i) =>
        ∃ h : j.val + 1 < ∑ i, k i,
          w j > w ⟨j.val + 1, h⟩)).card + 1 = p } := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (wmiWordFiberEquiv m k p)

end MetaMathlibExt

/--
[worpitzky_identity_multiset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean)
-/
@[path]
private lemma worpitzky_identity_multiset_eq
  {m : ℕ}
  {k : Fin m → ℕ}
  {x : ℕ} :
-- imply
  Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
    Finset.sum (Finset.Icc 1 (max 1 (Finset.sum Finset.univ (fun a => k a)))) (fun p =>
    Nat.choose (x + Finset.sum Finset.univ (fun a => k a) - p)
    (Finset.sum Finset.univ (fun a => k a)) *
    Nat.card { w : Fin (Finset.sum Finset.univ (fun a => k a)) → Fin m //
    (∀ i,
    Fintype.card
    { j : Fin (Finset.sum Finset.univ (fun a => k a)) // w j = i } = k i) ∧
    (Finset.univ.filter
    (fun j : Fin (Finset.sum Finset.univ (fun a => k a)) =>
    ∃ h : j.val + 1 < Finset.sum Finset.univ (fun a => k a),
    w j > w ⟨j.val + 1, h⟩)).card + 1 = p }) := by
-- proof
  apply MetaMathlibExt.worpitzky_identity_multiset m k x


-- created on 2026-10-20
-- updated on 2026-10-23
