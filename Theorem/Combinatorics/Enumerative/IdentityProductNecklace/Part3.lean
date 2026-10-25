/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.IdentityProductNecklace.Part4


section

namespace MetaMathlibExt

/-- The described set of necklaces is the range of `neckQuot`. -/
lemma neck_range (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (S : Set (Set (Fin n → G)))
    (hS : S = {O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧
      O = orbSet G n x}) :
    S = neckQuot G n '' Set.univ := by
  rw [hS]
  ext O
  constructor
  · rintro ⟨x, hx, hO⟩
    let q : Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1}) :=
      ⟦(⟨x, hx⟩ : {x : Fin n → G // (List.ofFn x).prod = 1})⟧
    refine ⟨q, Set.mem_univ _, ?_⟩
    have hex : (Quotient.out q :
        {x : Fin n → G // (List.ofFn x).prod = 1}) ≈ ⟨x, hx⟩ :=
      Quotient.exact (Quotient.out_eq _)
    have heq := orbSet_congr G n _ _ hex
    change orbSet G n (Quotient.out q).val = O
    rw [heq]
    exact hO.symm
  · rintro ⟨q, _, hO⟩
    exact ⟨(Quotient.out q).val, (Quotient.out q).prop, hO.symm⟩

/-- Cast of a mod is the original element in `ZMod n`. -/
lemma cast_mod_eq (n m : ℕ) : (((m % n : ℕ)) : ZMod n) = ((m : ℕ) : ZMod n) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq m n)

/-- Shifting by a multiple of `d` preserves the mod-`d` class, through a mod-`n` wrap. -/
lemma mod_shift_eq (i k d n : ℕ) (hdvd_n : d ∣ n) (hdvd_k : d ∣ k) :
    ((i + k) % n) % d = i % d := by
  rw [Nat.mod_mod_of_dvd _ hdvd_n]
  have hk0 : k % d = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd_k
  conv_lhs => rw [Nat.add_mod, hk0, Nat.add_zero, Nat.mod_mod]

/-- Bézout: the gcd is a multiple of `k` in `ZMod n`. -/
lemma bezout_eq (n : ℕ) [NeZero n] (k : ZMod n) :
    ((Nat.gcd n k.val : ℕ) : ZMod n)
      = ((Nat.gcdB n k.val : ℤ) : ZMod n) * k := by
  have h := Nat.gcd_eq_gcd_ab n k.val
  have h2 := congrArg (fun z : ℤ => (z : ZMod n)) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, zero_add] at h2
  rw [ZMod.natCast_zmod_val] at h2
  exact h2.trans (mul_comm _ _)

/-- A tuple fixed under single `c`-steps is fixed under any number of steps. -/
lemma iter_fixed (G : Type*)
    (n : ℕ) [NeZero n] (c : ℕ) (x : Fin n → G)
    (hfix : ∀ j : Fin n, x ⟨(j.val + c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = x j)
    (t u : ℕ) (hu : u < n) :
    x ⟨(u + t * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = x ⟨u, hu⟩ := by
  induction t with
  | zero =>
    have key0 : (u + 0 * c) % n = u := by
      rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hu]
    exact congrArg x (Fin.ext key0)
  | succ t ih =>
    have hstep : (u + (t * c + c)) % n = ((u + t * c) % n + c) % n := by
      have e : ((u + t * c) % n + c) % n = ((u + t * c) + c) % n := by
        conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hassoc : u + (t * c + c) = (u + t * c) + c := by ring
      rw [e, hassoc]
    have htc : (t + 1) * c = t * c + c := by ring
    have key : (u + (t + 1) * c) % n = ((u + t * c) % n + c) % n := by
      rw [htc]; exact hstep
    calc x ⟨(u + (t + 1) * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩
        = x ⟨((u + t * c) % n + c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
          congrArg x (Fin.ext key)
      _ = x ⟨(u + t * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
          hfix ⟨(u + t * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      _ = x ⟨u, hu⟩ := ih

/-- A tuple fixed under `k`-shifts is determined by its values on `0 .. d-1`. -/
lemma path_lemma (G : Type*)
    (n : ℕ) [NeZero n] (k : ZMod n) (x : Fin n → G)
    (hfix : ∀ j : Fin n, x ⟨(j.val + k.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      = x j) :
    ∀ i : Fin n, x i = x ⟨i.val % Nat.gcd n k.val,
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.gcd_pos_of_pos_left _ (NeZero.pos n)))
        (Nat.gcd_le_left _ (NeZero.pos n))⟩ := by
  have hnpos : 0 < n := NeZero.pos n
  set dd := Nat.gcd n k.val with hdd
  have hddpos : 0 < dd := Nat.gcd_pos_of_pos_left _ hnpos
  have hddle : dd ≤ n := Nat.gcd_le_left _ hnpos
  have hbez : ((dd : ℕ) : ZMod n) = ((Nat.gcdB n k.val : ℤ) : ZMod n) * k := by
    rw [hdd]
    exact bezout_eq n k
  intro i
  have hj0lt : i.val % dd < n :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hddpos) hddle
  set s : ZMod n := ((i.val / dd : ℕ) : ZMod n) * ((Nat.gcdB n k.val : ℤ) : ZMod n)
    with hs
  have hclaim : ((i.val : ℕ) : ZMod n)
      = ((i.val % dd : ℕ) : ZMod n) + s * k := by
    have hdecomp : i.val = i.val % dd + dd * (i.val / dd) := by
      have h := Nat.mod_add_div i.val dd
      omega
    conv_lhs => rw [hdecomp]
    push_cast
    rw [hbez, hs]
    ring
  have hstep := iter_fixed G n k.val x hfix s.val (i.val % dd) hj0lt
  have hXcast : (i.val % dd + s.val * k.val) % n = i.val := by
    have h1 : ((((i.val % dd + s.val * k.val) % n : ℕ))) = ((i.val : ℕ) : ZMod n) := by
      have h1a : ((((i.val % dd + s.val * k.val) % n : ℕ)) : ZMod n)
          = ((i.val % dd : ℕ) : ZMod n) + s * k := by
        rw [cast_mod_eq]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [h1a]
      exact hclaim.symm
    have hv1 := ZMod.val_natCast_of_lt (Nat.mod_lt _ hnpos :
      (i.val % dd + s.val * k.val) % n < n)
    have hv2 := ZMod.val_natCast_of_lt i.isLt
    have hcon := congrArg ZMod.val h1
    rwa [hv1, hv2] at hcon
  have hfin : (⟨(i.val % dd + s.val * k.val) % n,
      Nat.mod_lt _ hnpos⟩ : Fin n) = ⟨i.val, i.isLt⟩ := Fin.ext hXcast
  rw [hfin] at hstep
  exact hstep

/-- Any transversal tuple is fixed under `k`-shifts. -/
lemma transversal_fixed (G : Type*)
    (n : ℕ) (k : ZMod n) (d : ℕ) (hd : 0 < d)
    (hdvd_n : d ∣ n) (hdvd_k : d ∣ k.val) (a : Fin d → G) :
    ∀ i : Fin n, a ⟨((i.val + k.val) % n) % d, Nat.mod_lt _ hd⟩
      = a ⟨i.val % d, Nat.mod_lt _ hd⟩ := by
  intro i
  exact congrArg a (Fin.ext (mod_shift_eq i.val k.val d n hdvd_n hdvd_k))

/-- Product over a periodic tuple equals a power. -/
lemma block_prod (G : Type*) [Group G]
    (d : ℕ) (hd : 0 < d) (e : ℕ) (a : Fin d → G) :
    ∀ (n : ℕ) (x : Fin n → G), e * d = n →
    (∀ i, x i = a ⟨i.val % d, Nat.mod_lt _ hd⟩) →
    (List.ofFn x).prod = ((List.ofFn a).prod) ^ e := by
  induction e with
  | zero =>
    intro n x hn h
    have hn0 : n = 0 := by
      have h0 : 0 * d = n := hn
      rw [Nat.zero_mul] at h0
      exact h0.symm
    subst hn0
    rw [pow_zero]
    have hlen : (List.ofFn x).length = 0 := by rw [List.length_ofFn]
    rw [List.length_eq_zero_iff.mp hlen, List.prod_nil]
  | succ e ih =>
    intro n x hn h
    have hdecomp : (e + 1) * d = e * d + d := by ring
    have hn2 : n = e * d + d := hn.symm.trans hdecomp
    have hle : d ≤ n := by
      have h1 : d ≤ e * d + d := Nat.le_add_left _ _
      rwa [← hn2] at h1
    have htake : (List.ofFn x).take d = List.ofFn a := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_take, List.length_ofFn, List.length_ofFn,
          Nat.min_eq_left hle]
      · intro j h1 h2
        have hj : j < d := by
          have h1' := h1
          rwa [List.length_take, List.length_ofFn, Nat.min_eq_left hle] at h1'
        rw [List.getElem_take, List.getElem_ofFn, List.getElem_ofFn]
        have hxj := h ⟨j, by omega⟩
        have hmod : j % d = j := Nat.mod_eq_of_lt hj
        have hfin : (⟨j % d, Nat.mod_lt _ hd⟩ : Fin d) = ⟨j, by omega⟩ :=
          Fin.ext hmod
        rw [hfin] at hxj
        exact hxj
    set y : Fin (e * d) → G := fun i => x ⟨i.val + d, by
      have hbd := i.isLt
      omega⟩ with hydef
    have hdrop : (List.ofFn x).drop d = List.ofFn y := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_drop, List.length_ofFn, List.length_ofFn, hn2,
          Nat.add_sub_cancel]
      · intro j h1 h2
        have hj2 : j < e * d := by simpa [List.length_ofFn] using h2
        rw [List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
        have hdeq : d + j = j + d := by omega
        change x ⟨d + j, _⟩ = y ⟨j, _⟩
        change x ⟨d + j, _⟩ = x ⟨j + d, _⟩
        exact congrArg x (Fin.ext hdeq)
    have hy : ∀ i, y i = a ⟨i.val % d, Nat.mod_lt _ hd⟩ := by
      intro i
      change x ⟨i.val + d, _⟩ = a ⟨i.val % d, _⟩
      have hxi := h ⟨i.val + d, by
        have hbd := i.isLt
        omega⟩
      have hmodd : (i.val + d) % d = i.val % d := Nat.add_mod_right _ _
      have hfin : (⟨(i.val + d) % d, Nat.mod_lt _ hd⟩ : Fin d)
          = ⟨i.val % d, Nat.mod_lt _ hd⟩ := Fin.ext hmodd
      rw [hfin] at hxi
      exact hxi
    have ih' := ih (e * d) y rfl hy
    have hprod : (List.ofFn x).prod
        = ((List.ofFn a).prod) * ((List.ofFn y).prod) := by
      conv_lhs => rw [← List.take_append_drop d (List.ofFn x), List.prod_append,
        htake, hdrop]
    rw [hprod, ih', pow_succ']

end MetaMathlibExt
end
