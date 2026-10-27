import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Order.ErdosSzekeres.Part2
open MathlibExt.Combinatorics.Order.ErdosSzekeres


namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[subseqLen_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma subseqLen_le
  {N k : ℕ}
  {φ : Fin k → Fin N}
-- given
  (hidx : ∀ i j : Fin k, i < j → φ i < φ j) :
-- imply
  k ≤ N := by
-- proof
  have hinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    obtain h | h | h := lt_trichotomy i j
    · exact (ne_of_lt (hidx i j h)) hij
    · exact hne h
    · exact (ne_of_gt (hidx j i h)) hij
  have hcard := Fintype.card_le_of_injective φ hinj
  simp only [Fintype.card_fin] at hcard
  exact hcard

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[incrLen_isEnd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma incrLen_isEnd
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsIncrEnd f p (incrLen f p) :=
-- proof
  (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[decrLen_isEnd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma decrLen_isEnd
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsDecrEnd f p (decrLen f p) :=
-- proof
  (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[le_incrLen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma le_incrLen
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N}
  {k : ℕ}
-- given
  (h : IsIncrEnd f p k) :
-- imply
  k ≤ incrLen f p := by
-- proof
  obtain ⟨hk, φ, hsub, hlast⟩ := h
  have hkN : k ≤ N := subseqLen_le hsub.1
  have hmem : k ∈ (Finset.range (N + 1)).filter (IsIncrEnd f p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk, φ, hsub, hlast⟩
  exact Finset.le_max' _ k hmem

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[le_decrLen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma le_decrLen
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N}
  {k : ℕ}
-- given
  (h : IsDecrEnd f p k) :
-- imply
  k ≤ decrLen f p := by
-- proof
  obtain ⟨hk, φ, hsub, hlast⟩ := h
  have hkN : k ≤ N := subseqLen_le hsub.1
  have hmem : k ∈ (Finset.range (N + 1)).filter (IsDecrEnd f p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk, φ, hsub, hlast⟩
  exact Finset.le_max' _ k hmem

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[incrLen_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma incrLen_ge_one
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  1 ≤ incrLen f p :=
-- proof
  le_incrLen f p 1 ⟨by omega, fun _ => p, singleton_incr f p, rfl⟩

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[decrLen_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma decrLen_ge_one
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  1 ≤ decrLen f p :=
-- proof
  le_decrLen f p 1 ⟨by omega, fun _ => p, singleton_decr f p, rfl⟩

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[idx_le_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma idx_le_last
  {N k : ℕ}
  {q : Fin N}
  {φ : Fin k → Fin N}
  {i : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hik : i.val < k) :
-- imply
  φ ⟨i.val, hik⟩ ≤ q := by
-- proof
  have hval : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval
  obtain h | h := lt_or_eq_of_le hle
  · have hlt := hidx _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, hlast]

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[val_le_last_incr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma val_le_last_incr
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q : Fin N}
  {φ : Fin k → Fin N}
  {i : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hval : ∀ i j : Fin k, i < j → f (φ i) < f (φ j))
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hik : i.val < k) :
-- imply
  f (φ ⟨i.val, hik⟩) ≤ f q := by
-- proof
  have hval0 : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval0
  obtain h | h := lt_or_eq_of_le hle
  · have hlt := hval _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, hlast]

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[last_le_val_decr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma last_le_val_decr
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q : Fin N}
  {φ : Fin k → Fin N}
  {i : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hval : ∀ i j : Fin k, i < j → f (φ j) < f (φ i))
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hik : i.val < k) :
-- imply
  f q ≤ f (φ ⟨i.val, hik⟩) := by
-- proof
  have hval0 : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval0
  obtain h | h := lt_or_eq_of_le hle
  · have hlt := hval _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, ← hlast]

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[extend_idx](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma extend_idx
  {N k : ℕ}
  {q p : Fin N}
  {φ : Fin k → Fin N}
  {i j : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hqp : q < p)
  (hij : i < j) :
-- imply
  extendMap φ p i < extendMap φ p j := by
-- proof
  have hiv : i.val < j.val := Fin.lt_def.mp hij
  have hik : i.val < k := by omega
  change (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
    (if h : j.val < k then φ ⟨j.val, h⟩ else p)
  by_cases hjk : j.val < k
  · rw [dite_eq_left hik, dite_eq_left hjk]
    exact hidx _ _ (Fin.lt_def.mpr hiv)
  · rw [dite_eq_left hik, dite_eq_right hjk]
    exact lt_of_le_of_lt (idx_le_last hk hidx hlast hik) hqp

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[extend_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma extend_last
  {N k : ℕ}
  {φ : Fin k → Fin N}
  {p : Fin N}
-- given
  (hk1 : 0 < k + 1) :
-- imply
  extendMap φ p ⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ = p := by
-- proof
  have hval : (⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ : Fin (k + 1)).val =
    k + 1 - 1 := rfl
  have hneg : ¬ (⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ : Fin (k + 1)).val < k := by
    omega
  unfold extendMap
  exact dite_eq_right hneg

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[incrExtend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma incrExtend
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
  {φ : Fin k → Fin N}
-- given
  (hk : 0 < k)
  (hsub : IsIncrSubseq f k φ)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hqp : q < p)
  (hval : f q < f p) :
-- imply
  IsIncrEnd f p (k + 1) := by
-- proof
  refine ⟨by omega, extendMap φ p, ⟨?_, ?_⟩, extend_last φ (by omega)⟩
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
      (if h : j.val < k then φ ⟨j.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.1 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_le_of_lt (idx_le_last hk hsub.1 hlast hik) hqp
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change f (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
      f (if h : j.val < k then φ ⟨j.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.2 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_le_of_lt (val_le_last_incr hk hsub.2 hlast hik) hval

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[decrExtend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma decrExtend
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
  {φ : Fin k → Fin N}
-- given
  (hk : 0 < k)
  (hsub : IsDecrSubseq f k φ)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hqp : q < p)
  (hval : f p < f q) :
-- imply
  IsDecrEnd f p (k + 1) := by
-- proof
  refine ⟨by omega, extendMap φ p, ⟨?_, ?_⟩, extend_last φ (by omega)⟩
  · intro i j hij
    exact extend_idx hk hsub.1 hlast hqp i j hij
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change f (if h : j.val < k then φ ⟨j.val, h⟩ else p) <
      f (if h : i.val < k then φ ⟨i.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.2 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_lt_of_le hval (last_le_val_decr hk hsub.2 hlast hik)

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[incrMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma incrMono
  {N : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
-- given
  (hqp : q < p)
  (hval : f q < f p) :
-- imply
  incrLen f q < incrLen f p := by
-- proof
  obtain ⟨hk, φ, hsub, hlast⟩ := incrLen_isEnd f q
  have hle : incrLen f q + 1 ≤ incrLen f p :=
    le_incrLen f p _ (incrExtend hk hsub hlast hqp hval)
  omega

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[decrMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma decrMono
  {N : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
-- given
  (hqp : q < p)
  (hval : f p < f q) :
-- imply
  decrLen f q < decrLen f p := by
-- proof
  obtain ⟨hk, φ, hsub, hlast⟩ := decrLen_isEnd f q
  have hle : decrLen f q + 1 ≤ decrLen f p :=
    le_decrLen f p _ (decrExtend hk hsub hlast hqp hval)
  omega

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[truncIncr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma truncIncr
  {N k r : ℕ}
  {f : Fin N → ℝ}
  {φ : Fin k → Fin N}
-- given
  (hsub : IsIncrSubseq f k φ)
  (hrk : r ≤ k) :
-- imply
  ∃ φ' : Fin r → Fin N, IsIncrSubseq f r φ' :=
-- proof
  ⟨fun i => φ (Fin.castLE hrk i), fun _ _ hij => hsub.1 _ _ hij,
    fun _ _ hij => hsub.2 _ _ hij⟩

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[truncDecr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma truncDecr
  {N k s : ℕ}
  {f : Fin N → ℝ}
  {φ : Fin k → Fin N}
-- given
  (hsub : IsDecrSubseq f k φ)
  (hsk : s ≤ k) :
-- imply
  ∃ ψ : Fin s → Fin N, IsDecrSubseq f s ψ :=
-- proof
  ⟨fun i => φ (Fin.castLE hsk i), fun _ _ hij => hsub.1 _ _ hij,
    fun _ _ hij => hsub.2 _ _ hij⟩

end MathlibExt.Combinatorics.Order.ErdosSzekeres

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[erdos_szekeres](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
lemma erdos_szekeres
  {r s : ℕ}
  {f : Fin ((r - 1) * (s - 1) + 1) → ℝ}
-- given
  (hr : 0 < r)
  (hs : 0 < s)
  (hinj : Function.Injective f) :
-- imply
  (∃ φ : Fin r → Fin ((r - 1) * (s - 1) + 1),
    (∀ i j : Fin r, i < j → φ i < φ j) ∧
    (∀ i j : Fin r, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin s → Fin ((r - 1) * (s - 1) + 1),
    (∀ i j : Fin s, i < j → ψ i < ψ j) ∧
    (∀ i j : Fin s, i < j → f (ψ j) < f (ψ i))) := by
-- proof
  classical
  by_cases hr1 : r = 1
  · have hNpos : 0 < (r - 1) * (s - 1) + 1 := Nat.succ_pos _
    subst hr1
    refine Or.inl ⟨fun _ => ⟨0, hNpos⟩, ?_, ?_⟩ <;> intro i j hij <;>
      exact False.elim (fin1_false hij)
  · by_cases hs1 : s = 1
    · have hNpos : 0 < (r - 1) * (s - 1) + 1 := Nat.succ_pos _
      subst hs1
      refine Or.inr ⟨fun _ => ⟨0, hNpos⟩, ?_, ?_⟩ <;> intro i j hij <;>
        exact False.elim (fin1_false hij)
    · have hr2 : 1 < r := by omega
      have hs2 : 1 < s := by omega
      by_cases ha : ∃ p, r ≤ incrLen f p
      · obtain ⟨p, hp⟩ := ha
        obtain ⟨_, φ, hsub, _⟩ := incrLen_isEnd f p
        obtain ⟨φ', hsub'⟩ := truncIncr hsub hp
        exact Or.inl ⟨φ', hsub'.1, hsub'.2⟩
      · by_cases hb : ∃ p, s ≤ decrLen f p
        · obtain ⟨p, hp⟩ := hb
          obtain ⟨_, φ, hsub, _⟩ := decrLen_isEnd f p
          obtain ⟨ψ, hsub'⟩ := truncDecr hsub hp
          exact Or.inr ⟨ψ, hsub'.1, hsub'.2⟩
        · have ha' : ∀ p, incrLen f p < r :=
          fun p => not_le.mp (fun h => ha ⟨p, h⟩)
          have hb' : ∀ p, decrLen f p < s :=
            fun p => not_le.mp (fun h => hb ⟨p, h⟩)
          have hmem1 : ∀ p : Fin ((r - 1) * (s - 1) + 1),
            incrLen f p - 1 < r - 1 := by
            intro p
            have h1 := incrLen_ge_one f p
            have h2 := ha' p
            omega
          have hmem2 : ∀ p : Fin ((r - 1) * (s - 1) + 1),
            decrLen f p - 1 < s - 1 := by
            intro p
            have h1 := decrLen_ge_one f p
            have h2 := hb' p
            omega
          have hcard :
            (Finset.univ : Finset (Fin (r - 1) × Fin (s - 1))).card <
            (Finset.univ : Finset (Fin ((r - 1) * (s - 1) + 1))).card := by
            rw [Finset.card_univ, Finset.card_univ, Fintype.card_prod,
              Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
            exact Nat.lt_succ_self _
          have hmap : Set.MapsTo
            (fun p : Fin ((r - 1) * (s - 1) + 1) =>
              ((⟨incrLen f p - 1, hmem1 p⟩ : Fin (r - 1)),
                (⟨decrLen f p - 1, hmem2 p⟩ : Fin (s - 1))))
            ↑(Finset.univ : Finset (Fin ((r - 1) * (s - 1) + 1)))
            ↑(Finset.univ : Finset (Fin (r - 1) × Fin (s - 1))) := by
            intro x _
            exact Finset.mem_univ _
          obtain ⟨x, _, y, _, hne, heq⟩ :=
            Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmap
          have ha_mk : (⟨incrLen f x - 1, hmem1 x⟩ : Fin (r - 1)) =
            ⟨incrLen f y - 1, hmem1 y⟩ :=
            congrArg Prod.fst heq
          have hb_mk : (⟨decrLen f x - 1, hmem2 x⟩ : Fin (s - 1)) =
            ⟨decrLen f y - 1, hmem2 y⟩ :=
            congrArg Prod.snd heq
          have ha_sub : incrLen f x - 1 = incrLen f y - 1 :=
            Fin.ext_iff.mp ha_mk
          have hb_sub : decrLen f x - 1 = decrLen f y - 1 :=
            Fin.ext_iff.mp hb_mk
          have ha_eq : incrLen f x = incrLen f y := by
            have h1 := incrLen_ge_one f x
            have h2 := incrLen_ge_one f y
            omega
          have hb_eq : decrLen f x = decrLen f y := by
            have h1 := decrLen_ge_one f x
            have h2 := decrLen_ge_one f y
            omega
          have hval_ne : x.val ≠ y.val := fun h => hne (Fin.ext_iff.mpr h)
          obtain hlt | heq_val | hgt := lt_trichotomy x.val y.val
          · have hxy : x < y := Fin.lt_def.mpr hlt
            have hfne : f x ≠ f y := fun h => hne (hinj h)
            obtain hltf | heqf | hgtf := lt_trichotomy (f x) (f y)
            · exfalso
              have hm := incrMono f hxy hltf
              omega
            · exact absurd heqf hfne
            · exfalso
              have hm := decrMono f hxy hgtf
              omega
          · exact absurd heq_val hval_ne
          · have hyx : y < x := Fin.lt_def.mpr hgt
            have hfne : f y ≠ f x := fun h => hne (hinj h).symm
            obtain hltf | heqf | hgtf := lt_trichotomy (f y) (f x)
            · exfalso
              have hm := incrMono f hyx hltf
              omega
            · exact absurd heqf hfne
            · exfalso
              have hm := decrMono f hyx hgtf
              omega

end MathlibExt.Combinatorics.Order.ErdosSzekeres

/--
[sub_one_lt_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma sub_one_lt_of_pos_eq
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  k - 1 < k := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.sub_one_lt_of_pos hk

/--
[fin1_false](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma fin1_false_eq
  {i j : Fin 1}
-- given
  (hij : i < j) :
-- imply
  False := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.fin1_false hij

/--
[singleton_incr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma singleton_incr_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsIncrSubseq f 1 (fun _ => p) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.singleton_incr f p

/--
[singleton_decr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma singleton_decr_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsDecrSubseq f 1 (fun _ => p) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.singleton_decr f p


-- created on 2026-10-20
-- updated on 2026-10-26
