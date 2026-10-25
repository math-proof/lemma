/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin
import Instance.Combinatorics.Enumerative.WorpitzkyMultisetIdentity


section

namespace MetaMathlibExt

theorem mono_gap {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (b : ℕ)
    (hb : b + 1 < K) :
    (e ⟨b, by omega⟩).val + desInd w b ≤
      (e ⟨b + 1, hb⟩).val := by
  have hdes : desInd w b =
      (if w ⟨b, by omega⟩ > w ⟨b + 1, hb⟩ then 1 else 0) := by
    unfold desInd
    simp only [hb, dite_true]
  rw [hdes]
  by_cases hw : w ⟨b, by omega⟩ > w ⟨b + 1, hb⟩
  · simp only [hw, ite_true]
    have hlt : e ⟨b, by omega⟩ < e ⟨b + 1, hb⟩ :=
      hmono.2 ⟨b, by omega⟩ hb hw
    have hval :
        (e ⟨b, by omega⟩).val < (e ⟨b + 1, hb⟩).val :=
      Fin.lt_def.mp hlt
    omega
  · simp only [hw, ite_false]
    have hle : (⟨b, by omega⟩ : Fin K) ≤ ⟨b + 1, hb⟩ := by
      change b ≤ b + 1
      omega
    have hle_e : e ⟨b, by omega⟩ ≤ e ⟨b + 1, hb⟩ :=
      hmono.1 hle
    have hval :
        (e ⟨b, by omega⟩).val ≤ (e ⟨b + 1, hb⟩).val :=
      Fin.le_iff_val_le_val.mp hle_e
    omega

theorem mono_lower {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (n : ℕ)
    (hn : n < K) : desPrefix w n ≤ (e ⟨n, hn⟩).val := by
  induction n with
  | zero =>
    rw [desPrefix_zero]
    omega
  | succ n ih =>
    have hn' : n < K := by omega
    have hih := ih hn'
    have hgap := mono_gap hmono n hn
    have heq : (e ⟨n, hn'⟩).val = (e ⟨n, by omega⟩).val := rfl
    rw [desPrefix_succ]
    omega

theorem desPrefix_last {m K : ℕ} (w : Fin K → Fin m)
    (hK : 0 < K) : desPrefix w K = desPrefix w (K - 1) := by
  have hK1 : K - 1 + 1 = K := by omega
  have hKK : K = K - 1 + 1 := hK1.symm
  have h1 : desPrefix w K = desPrefix w (K - 1 + 1) :=
    congrArg (desPrefix w) hKK
  rw [h1, desPrefix_succ]
  have h0 : desInd w (K - 1) = 0 := by
    apply desInd_eq_zero_of_ge
    omega
  rw [h0, Nat.add_zero]

theorem mono_leap {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (a b : ℕ)
    (hab : a ≤ b) (hb : b < K) (ha : a < K) :
    (e ⟨a, ha⟩).val + (desPrefix w b - desPrefix w a) ≤
      (e ⟨b, hb⟩).val := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp only [Nat.sub_self, Nat.add_zero]
    exact Nat.le_refl _
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq
      simp only [Nat.sub_self, Nat.add_zero]
      exact Nat.le_refl _
    · have hab' : a ≤ b := by omega
      have hb' : b < K := by omega
      have hih := ih hab' hb'
      have hgap := mono_gap hmono b hb
      have hle : desPrefix w a ≤ desPrefix w b :=
        (desPrefix_mono w) hab'
      have hsucc : desPrefix w (b + 1) =
          desPrefix w b + desInd w b :=
        desPrefix_succ w b
      have heq_b : (e ⟨b, hb'⟩).val =
          (e ⟨b, by omega⟩).val := rfl
      omega

theorem mono_upper {m K x : ℕ} {w : Fin K → Fin m}
    {e : Fin K → Fin x} (hmono : IsMono w e) (n : ℕ)
    (hn : n < K) :
    (e ⟨n, hn⟩).val + (desPrefix w K - desPrefix w n) < x := by
  have hK : 0 < K := by omega
  have hle_n : n ≤ K - 1 := by omega
  have hb : K - 1 < K := by omega
  have hleap := mono_leap hmono n (K - 1) hle_n hb hn
  have hlast : desPrefix w K = desPrefix w (K - 1) :=
    desPrefix_last w hK
  have hlt : (e ⟨K - 1, hb⟩).val < x := (e ⟨K - 1, hb⟩).isLt
  omega

end MetaMathlibExt
end
