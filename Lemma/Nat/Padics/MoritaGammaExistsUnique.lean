import Mathlib
import sympy.Basic
import Theorem.NumberTheory.Padics.MoritaGammaExistsUnique.Part2
open MetaMathlibExt


namespace MetaMathlibExt

/--
[orderOf_neg_one_units_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma orderOf_neg_one_units_prime_pow (p s : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
  orderOf (-1 : (ZMod (p ^ (s + 1)))ˣ) = 2 := by
  have h1 : (-1 : (ZMod (p ^ (s + 1)))ˣ) ≠ 1 := by
    rw [Ne, Units.ext_iff]
    simp only [Units.val_neg, Units.val_one]
    have h23 : 2 < p ^ (s + 1) := by
      have h2le := (Fact.out : p.Prime).two_le
      have h3 : 3 ≤ p := by omega
      calc 2 < 3 := by norm_num
        _ ≤ p := h3
        _ ≤ p ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) p
    have : Fact (2 < p ^ (s + 1)) := ⟨h23⟩
    exact ZMod.neg_one_ne_one
  have h2 : (-1 : (ZMod (p ^ (s + 1)))ˣ) ^ 2 = 1 := by
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, neg_one_sq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h2 h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sq_eq_one_iff_units_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma sq_eq_one_iff_units_prime_pow (p s : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
  (x : (ZMod (p ^ (s + 1)))ˣ) (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : IsCyclic (ZMod (p ^ (s + 1)))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 (s + 1)
  have hneg : orderOf (-1 : (ZMod (p ^ (s + 1)))ˣ) = 2 :=
    orderOf_neg_one_units_prime_pow p s hp2
  have h2dvd : 2 ∣ Fintype.card (ZMod (p ^ (s + 1)))ˣ := hneg ▸ orderOf_dvd_card
  have hcount : (Finset.univ.filter
    (fun a : (ZMod (p ^ (s + 1)))ˣ => orderOf a = 2)).card = 1 :=
    (IsCyclic.card_orderOf_eq_totient (α := (ZMod (p ^ (s + 1)))ˣ) (d := 2) h2dvd).trans
      Nat.totient_two
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcount
  have hx2 : orderOf x = 1 ∨ orderOf x = 2 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hx
    obtain h | h := (Nat.dvd_prime Nat.prime_two).mp hdvd
    · exact Or.inl h
    · exact Or.inr h
  obtain h | h := hx2
  · exact Or.inl (orderOf_eq_one_iff.mp h)
  · have hxm : x ∈ ({a} : Finset (ZMod (p ^ (s + 1)))ˣ) := by
    rw [← ha]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩
    have hnm : (-1 : (ZMod (p ^ (s + 1)))ˣ) ∈ ({a} : Finset (ZMod (p ^ (s + 1)))ˣ) := by
      rw [← ha]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg⟩
    rw [Finset.mem_singleton] at hxm hnm
    exact Or.inr (hxm.trans hnm.symm)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prod_units_zmod_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma prod_units_zmod_prime_pow (p s : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
  ∏ u : (ZMod (p ^ (s + 1)))ˣ, (u : ZMod (p ^ (s + 1))) = -1 := by
  classical
  have h1lt : 1 < p ^ (s + 1) := by
    have h2le := (Fact.out : p.Prime).two_le
    calc 1 < 2 := by norm_num
      _ ≤ p := h2le
      _ ≤ p ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) p
  have : Fact (1 < p ^ (s + 1)) := ⟨h1lt⟩
  have key := sq_eq_one_iff_units_prime_pow p s hp2
  have hg1 : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
    (_ : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
    ((a : ZMod (p ^ (s + 1))) * (((a⁻¹ : (ZMod (p ^ (s + 1)))ˣ)) : ZMod (p ^ (s + 1))) = 1) := by
    intro a _
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg3 : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
    (ha : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
    ((a : ZMod (p ^ (s + 1))) ≠ 1 → a⁻¹ ≠ a) := by
    intro a ha hne hcon
    apply hne
    have hmem : a ≠ (-1 : (ZMod (p ^ (s + 1)))ˣ) := (Finset.mem_erase.mp ha).1
    have hmul : a * a = a * a⁻¹ := by rw [hcon]
    have hsq : a ^ 2 = 1 := by
      rw [sq, hmul]
      exact mul_inv_cancel a
    obtain h | h := key a hsq
    · rw [h]
      rfl
    · exact absurd h hmem
  have hgmem : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
    (ha : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
    a⁻¹ ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ) := by
    intro a ha
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hcon
    have hmem : a ≠ (-1 : (ZMod (p ^ (s + 1)))ˣ) := (Finset.mem_erase.mp ha).1
    apply hmem
    have h1 : a = a⁻¹⁻¹ := (inv_inv a).symm
    rw [h1, hcon]
    apply Units.ext
    simp
  have hg4 : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
    (ha : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
    (a⁻¹⁻¹ : (ZMod (p ^ (s + 1)))ˣ) = a := by
    intro a _
    exact inv_inv a
  have hrest : ∏ x ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ),
    (x : ZMod (p ^ (s + 1))) = 1 :=
    Finset.prod_involution (fun x _ => x⁻¹) hg1 hg3 hgmem hg4
  have hmem : (-1 : (ZMod (p ^ (s + 1)))ˣ) ∈ Finset.univ := Finset.mem_univ _
  conv_lhs => rw [← Finset.insert_erase hmem,
    Finset.prod_insert (Finset.notMem_erase _ _), hrest, mul_one]
  simp [Units.val_neg, Units.val_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coe_unitOfNotDvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma coe_unitOfNotDvd (p s k : ℕ) [Fact p.Prime] (hk : ¬ p ∣ k) :
  ((unitOfNotDvd p s k hk : (ZMod (p ^ (s + 1)))ˣ) : ZMod (p ^ (s + 1))) =
    (k : ZMod (p ^ (s + 1))) := by
  unfold unitOfNotDvd
  exact IsUnit.unit_spec _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prod_range_filter_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma prod_range_filter_prime_pow (p s : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
  ∏ k ∈ (Finset.range (p ^ (s + 1))).filter (fun k => ¬ p ∣ k),
    (k : ZMod (p ^ (s + 1))) = -1 := by
  have hpos : 0 < s + 1 := Nat.succ_pos s
  have h1lt : 1 < p ^ (s + 1) := by
    have h2le := (Fact.out : p.Prime).two_le
    calc 1 < 2 := by norm_num
      _ ≤ p := h2le
      _ ≤ p ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) p
  have : Fact (1 < p ^ (s + 1)) := ⟨h1lt⟩
  have : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← prod_units_zmod_prime_pow p s hp2]
  apply Finset.prod_bij (fun k hk => unitOfNotDvd p s k (Finset.mem_filter.mp hk).2)
  · intro a _
    exact Finset.mem_univ _
  · intro a1 ha1 a2 ha2 heq
    have h1 : a1 ∈ Finset.range (p ^ (s + 1)) := (Finset.mem_filter.mp ha1).1
    have h2 : a2 ∈ Finset.range (p ^ (s + 1)) := (Finset.mem_filter.mp ha2).1
    have hce : (a1 : ZMod (p ^ (s + 1))) = (a2 : ZMod (p ^ (s + 1))) := by
      have hcon := congrArg (fun u : (ZMod (p ^ (s + 1)))ˣ => (u : ZMod (p ^ (s + 1)))) heq
      rwa [coe_unitOfNotDvd, coe_unitOfNotDvd] at hcon
    have hmod : a1 ≡ a2 [MOD p ^ (s + 1)] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hce
    exact Nat.ModEq.eq_of_lt_of_lt hmod (Finset.mem_range.mp h1) (Finset.mem_range.mp h2)
  · intro b _
    set a : ℕ := ZMod.val (b : ZMod (p ^ (s + 1))) with ha_def
    have hlt : a < p ^ (s + 1) := ha_def ▸ ZMod.val_lt _
    have hcast : (a : ZMod (p ^ (s + 1))) = (b : ZMod (p ^ (s + 1))) := by
      rw [ha_def, ZMod.natCast_val, ZMod.cast_id]
    have hunit : IsUnit (a : ZMod (p ^ (s + 1))) := hcast.symm ▸ b.isUnit
    have hndvd : ¬ p ∣ a :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := s + 1) (a := a) Fact.out
        hpos).mp hunit
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hndvd⟩, ?_⟩
    apply Units.ext
    rwa [coe_unitOfNotDvd]
  · intro a ha
    exact (coe_unitOfNotDvd p s a (Finset.mem_filter.mp ha).2).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prod_Ico_filter_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma prod_Ico_filter_prime_pow (p s m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
  ∏ k ∈ (Finset.Ico m (m + p ^ (s + 1))).filter (fun k => ¬ p ∣ k),
    (k : ZMod (p ^ (s + 1))) = -1 := by
  have hpos : 0 < s + 1 := Nat.succ_pos s
  have hPpos : 0 < p ^ (s + 1) := pow_pos (Fact.out : p.Prime).pos _
  have : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← prod_units_zmod_prime_pow p s hp2]
  apply Finset.prod_bij (fun k hk => unitOfNotDvd p s k (Finset.mem_filter.mp hk).2)
  · intro a _
    exact Finset.mem_univ _
  · intro a1 ha1 a2 ha2 heq
    have hce : (a1 : ZMod (p ^ (s + 1))) = (a2 : ZMod (p ^ (s + 1))) := by
      have hcon := congrArg (fun u : (ZMod (p ^ (s + 1)))ˣ => (u : ZMod (p ^ (s + 1)))) heq
      rwa [coe_unitOfNotDvd, coe_unitOfNotDvd] at hcon
    have hm1 := Finset.mem_Ico.mp (Finset.mem_filter.mp ha1).1
    have hm2 := Finset.mem_Ico.mp (Finset.mem_filter.mp ha2).1
    have hj : ((a1 - m : ℕ) : ZMod (p ^ (s + 1))) =
      ((a2 - m : ℕ) : ZMod (p ^ (s + 1))) := by
      rw [Nat.cast_sub hm1.1, Nat.cast_sub hm2.1, hce]
    have hmod : (a1 - m) ≡ (a2 - m) [MOD p ^ (s + 1)] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hj
    have hjj := Nat.ModEq.eq_of_lt_of_lt hmod (by omega : a1 - m < p ^ (s + 1))
      (by omega : a2 - m < p ^ (s + 1))
    omega
  · intro b _
    set a : ℕ := m + ((ZMod.val (b : ZMod (p ^ (s + 1))) + p ^ (s + 1) -
      m % p ^ (s + 1)) % p ^ (s + 1)) with ha_def
    have hmemIco : a ∈ Finset.Ico m (m + p ^ (s + 1)) := by
      rw [ha_def]
      exact Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _,
        Nat.add_lt_add_left (Nat.mod_lt _ hPpos) _⟩
    have hcast : (a : ZMod (p ^ (s + 1))) = (b : ZMod (p ^ (s + 1))) := by
      have hv : (ZMod.val (b : ZMod (p ^ (s + 1))) : ZMod (p ^ (s + 1))) =
        (b : ZMod (p ^ (s + 1))) := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      have hr : (m % p ^ (s + 1) : ZMod (p ^ (s + 1))) = (m : ZMod (p ^ (s + 1))) :=
        ZMod.natCast_mod _ _
      have hle : m % p ^ (s + 1) ≤
        ZMod.val (b : ZMod (p ^ (s + 1))) + p ^ (s + 1) :=
        Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hPpos)) (Nat.le_add_left _ _)
      rw [ha_def, Nat.cast_add, ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add,
        ZMod.natCast_self, hr, hv]
      ring
    have hunit : IsUnit (a : ZMod (p ^ (s + 1))) := by
      rwa [hcast]
    have hndvd : ¬ p ∣ a :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := s + 1) (a := a) Fact.out
        hpos).mp hunit
    refine ⟨a, Finset.mem_filter.mpr ⟨hmemIco, hndvd⟩, ?_⟩
    apply Units.ext
    rwa [coe_unitOfNotDvd]
  · intro a ha
    exact (coe_unitOfNotDvd p s a (Finset.mem_filter.mp ha).2).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[core_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma core_congr (p s m n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hmn : m ≤ n)
  (hdvd : p ^ (s + 1) ∣ n - m) :
  (-1 : ZMod (p ^ (s + 1))) ^ (n - m) *
    ∏ k ∈ (Finset.Ico m n).filter (fun k => ¬ p ∣ k), (k : ZMod (p ^ (s + 1))) = 1 := by
  obtain ⟨t, ht⟩ := hdvd
  have ht' : n - m = t * p ^ (s + 1) := ht.trans (mul_comm _ _)
  have hnm : n = m + t * p ^ (s + 1) := by omega
  rw [hnm]
  clear ht ht' hmn hnm
  induction t generalizing m with
  | zero =>
    have hI : Finset.Ico m (m + 0 * p ^ (s + 1)) = ∅ := by simp
    rw [hI]
    simp
  | succ t ih =>
    have htp : (t + 1) * p ^ (s + 1) = t * p ^ (s + 1) + p ^ (s + 1) := by ring
    have hend : m + (t + 1) * p ^ (s + 1) = (m + t * p ^ (s + 1)) + p ^ (s + 1) := by
      rw [htp]
      omega
    have h1 : m ≤ m + t * p ^ (s + 1) := Nat.le_add_right _ _
    have h2 : m + t * p ^ (s + 1) ≤ (m + t * p ^ (s + 1)) + p ^ (s + 1) :=
      Nat.le_add_right _ _
    have hsplit : ((Finset.Ico m ((m + t * p ^ (s + 1)) + p ^ (s + 1))).filter
      (fun k => ¬ p ∣ k)) =
      ((Finset.Ico m (m + t * p ^ (s + 1))).filter (fun k => ¬ p ∣ k)) ∪
      ((Finset.Ico (m + t * p ^ (s + 1)) ((m + t * p ^ (s + 1)) + p ^ (s + 1))).filter
        (fun k => ¬ p ∣ k)) := by
      rw [← Finset.filter_union, ← Finset.Ico_union_Ico_eq_Ico h1 h2]
    have hdisj : Disjoint
      (((Finset.Ico m (m + t * p ^ (s + 1))).filter (fun k => ¬ p ∣ k)))
      (((Finset.Ico (m + t * p ^ (s + 1)) ((m + t * p ^ (s + 1)) + p ^ (s + 1))).filter
        (fun k => ¬ p ∣ k))) :=
      Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        (Finset.Ico_disjoint_Ico_consecutive _ _ _)
    have hexp : (m + t * p ^ (s + 1)) + p ^ (s + 1) - m =
      (m + t * p ^ (s + 1) - m) + p ^ (s + 1) := by omega
    rw [hend, hsplit, Finset.prod_union hdisj, hexp,
      pow_add (-1 : ZMod (p ^ (s + 1))) _ _]
    have e1 : (-1 : ZMod (p ^ (s + 1))) ^ (m + t * p ^ (s + 1) - m) *
      ∏ k ∈ (Finset.Ico m (m + t * p ^ (s + 1))).filter (fun k => ¬ p ∣ k),
        (k : ZMod (p ^ (s + 1))) = 1 := ih m
    have hPodd : Odd (p ^ (s + 1)) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
    have hnegP : (-1 : ZMod (p ^ (s + 1))) ^ (p ^ (s + 1)) = -1 := hPodd.neg_one_pow
    have hblock := prod_Ico_filter_prime_pow p s (m + t * p ^ (s + 1)) hp2
    have e2 : (-1 : ZMod (p ^ (s + 1))) ^ (p ^ (s + 1)) *
      ∏ k ∈ (Finset.Ico (m + t * p ^ (s + 1)) ((m + t * p ^ (s + 1)) + p ^ (s + 1))).filter
        (fun k => ¬ p ∣ k), (k : ZMod (p ^ (s + 1))) = 1 := by
      rw [hnegP, hblock]
      ring
    have hrearr : (-1 : ZMod (p ^ (s + 1))) ^ (m + t * p ^ (s + 1) - m) *
      (-1 : ZMod (p ^ (s + 1))) ^ (p ^ (s + 1)) *
      ((∏ k ∈ (Finset.Ico m (m + t * p ^ (s + 1))).filter (fun k => ¬ p ∣ k),
        (k : ZMod (p ^ (s + 1)))) *
      ∏ k ∈ (Finset.Ico (m + t * p ^ (s + 1)) ((m + t * p ^ (s + 1)) + p ^ (s + 1))).filter
        (fun k => ¬ p ∣ k), (k : ZMod (p ^ (s + 1)))) =
      (((-1 : ZMod (p ^ (s + 1))) ^ (m + t * p ^ (s + 1) - m) *
      ∏ k ∈ (Finset.Ico m (m + t * p ^ (s + 1))).filter (fun k => ¬ p ∣ k),
        (k : ZMod (p ^ (s + 1)))) *
      (((-1 : ZMod (p ^ (s + 1))) ^ (p ^ (s + 1))) *
      ∏ k ∈ (Finset.Ico (m + t * p ^ (s + 1)) ((m + t * p ^ (s + 1)) + p ^ (s + 1))).filter
        (fun k => ¬ p ∣ k), (k : ZMod (p ^ (s + 1))))) := by
      ring
    rw [hrearr, e1, e2, mul_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[est_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma est_le (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k m n : ℕ) (hmn : m ≤ n)
  (h : ‖(m : PadicInt p) - (n : PadicInt p)‖ ≤ (p : ℝ) ^ (-((k : ℕ) : ℤ))) :
  ‖moritaGammaNat p m - moritaGammaNat p n‖ ≤ (p : ℝ) ^ (-((k : ℕ) : ℤ)) := by
  obtain _ | s := k
  · simpa using PadicInt.norm_le_one (moritaGammaNat p m - moritaGammaNat p n)
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow] at h ⊢
    have h0 : PadicInt.toZModPow (s + 1) ((m : PadicInt p) - (n : PadicInt p)) = 0 := by
      apply RingHom.mem_ker.mp
      rwa [PadicInt.ker_toZModPow]
    rw [map_sub] at h0
    simp only [map_natCast] at h0
    have hmod : (m : ZMod (p ^ (s + 1))) = (n : ZMod (p ^ (s + 1))) := sub_eq_zero.mp h0
    have hMe : m ≡ n [MOD p ^ (s + 1)] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
    have hdvd : p ^ (s + 1) ∣ n - m := (Nat.modEq_iff_dvd' hmn).mp hMe
    have hcore := core_congr p s m n hp2 hmn hdvd
    have hmap : ∀ j : ℕ, PadicInt.toZModPow (s + 1) (moritaGammaNat p j) =
      (-1 : ZMod (p ^ (s + 1))) ^ j *
      ∏ i ∈ (Finset.range j).filter (fun i => ¬ p ∣ i), (i : ZMod (p ^ (s + 1))) := by
      intro j
      unfold moritaGammaNat
      rw [map_mul, map_pow]
      congr 1
      · rw [map_neg, map_one]
      · rw [map_prod]
        apply Finset.prod_congr rfl
        intro i _
        exact map_natCast _ _
    have hsplit : ∏ i ∈ (Finset.range n).filter (fun i => ¬ p ∣ i),
      (i : ZMod (p ^ (s + 1))) =
      (∏ i ∈ (Finset.range m).filter (fun i => ¬ p ∣ i), (i : ZMod (p ^ (s + 1)))) *
      (∏ i ∈ (Finset.Ico m n).filter (fun i => ¬ p ∣ i), (i : ZMod (p ^ (s + 1)))) := by
      have hU : ((Finset.range n).filter (fun i => ¬ p ∣ i)) =
        ((Finset.range m).filter (fun i => ¬ p ∣ i)) ∪
        ((Finset.Ico m n).filter (fun i => ¬ p ∣ i)) := by
        rw [← Finset.filter_union, Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le m) hmn]
      have hdisj' : Disjoint ((Finset.range m).filter (fun i => ¬ p ∣ i))
        ((Finset.Ico m n).filter (fun i => ¬ p ∣ i)) := by
        rw [Finset.range_eq_Ico]
        exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          (Finset.Ico_disjoint_Ico_consecutive _ _ _)
      rw [hU, Finset.prod_union hdisj']
    have hexpN : (-1 : ZMod (p ^ (s + 1))) ^ n =
      (-1 : ZMod (p ^ (s + 1))) ^ m * (-1 : ZMod (p ^ (s + 1))) ^ (n - m) := by
      have hexp : n = m + (n - m) := (Nat.add_sub_cancel' hmn).symm
      conv_lhs => rw [hexp]
      rw [pow_add (-1 : ZMod (p ^ (s + 1))) m (n - m)]
    have hfin : PadicInt.toZModPow (s + 1) (moritaGammaNat p m - moritaGammaNat p n) = 0 := by
      rw [map_sub, hmap m, hmap n, hsplit, hexpN]
      have hfact : ∀ (A B C D : ZMod (p ^ (s + 1))), C * D = 1 →
        A * B - (A * C) * (B * D) = 0 := by
        intro A B C D hCD
        have hCD' : (A * C) * (B * D) = (A * B) * (C * D) := by ring
        rw [hCD', hCD, mul_one, sub_self]
      exact hfact _ _ _ _ hcore
    rw [← PadicInt.ker_toZModPow]
    exact RingHom.mem_ker.mp hfin

end MetaMathlibExt

namespace MetaMathlibExt

/--
[est](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma est (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k m n : ℕ)
  (h : ‖(m : PadicInt p) - (n : PadicInt p)‖ ≤ (p : ℝ) ^ (-((k : ℕ) : ℤ))) :
  ‖moritaGammaNat p m - moritaGammaNat p n‖ ≤ (p : ℝ) ^ (-((k : ℕ) : ℤ)) := by
  obtain hle | hle := le_total m n
  · exact est_le p hp2 k m n hle h
  · have h' : ‖(n : PadicInt p) - (m : PadicInt p)‖ ≤ (p : ℝ) ^ (-((k : ℕ) : ℤ)) := by
    rwa [norm_sub_rev (n : PadicInt p) (m : PadicInt p)]
    have hfin := est_le p hp2 k n m hle h'
    rwa [norm_sub_rev (moritaGammaNat p m) (moritaGammaNat p n)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[norm_natCast_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma norm_natCast_of_not_dvd (p k : ℕ) [Fact p.Prime] (hk : ¬ p ∣ k) :
  ‖(k : PadicInt p)‖ = 1 := by
  by_contra hne
  have hlt : ‖(k : PadicInt p)‖ < 1 :=
    lt_of_le_of_ne (PadicInt.norm_le_one _) hne
  have hdvd : (p : PadicInt p) ∣ (k : PadicInt p) :=
    (PadicInt.norm_lt_one_iff_dvd _).mp hlt
  have h0 : (k : ZMod p) = 0 := by
    have hmap := map_dvd PadicInt.toZMod hdvd
    simp only [map_natCast] at hmap
    rw [ZMod.natCast_self] at hmap
    exact zero_dvd_iff.mp hmap
  have hMe : k ≡ 0 [MOD p] := (ZMod.natCast_eq_natCast_iff k 0 p).mp (by simpa using h0)
  exact hk ((Nat.modEq_zero_iff_dvd).mp hMe)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[norm_moritaGammaNat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma norm_moritaGammaNat (p n : ℕ) [Fact p.Prime] : ‖moritaGammaNat p n‖ = 1 := by
  unfold moritaGammaNat
  rw [norm_mul]
  have h1 : ‖(-1 : PadicInt p) ^ n‖ = 1 := by simp
  rw [h1, one_mul, norm_prod]
  apply Finset.prod_eq_one
  intro k hk
  exact norm_natCast_of_not_dvd p k (Finset.mem_filter.mp hk).2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[moritaGammaPre_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma moritaGammaPre_eq (p : ℕ) [Fact p.Prime]
  (b : {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)}) (n : ℕ)
  (hn : b.val = (n : PadicInt p)) : moritaGammaPre p b = moritaGammaNat p n := by
  unfold moritaGammaPre
  have hex : ∃ a : ℕ, ((a : PadicInt p)) = b.val := b.2
  have h1 : ((Function.invFun ((↑) : ℕ → PadicInt p) b.val : ℕ) : PadicInt p) = b.val :=
    Function.invFun_eq hex
  have h : Function.invFun ((↑) : ℕ → PadicInt p) b.val = n := by
    apply Nat.cast_injective (R := PadicInt p)
    rw [h1, hn]
  rw [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[uniformContinuous_moritaGammaPre](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma uniformContinuous_moritaGammaPre (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
  UniformContinuous (moritaGammaPre p) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨(p : ℝ) ^ (-((k : ℕ) : ℤ)),
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, ?_⟩
  intro x y hxy
  obtain ⟨m, hm⟩ := x.2
  obtain ⟨n, hn⟩ := y.2
  have hFx : moritaGammaPre p x = moritaGammaNat p m := moritaGammaPre_eq p x m hm.symm
  have hFy : moritaGammaPre p y = moritaGammaNat p n := moritaGammaPre_eq p y n hn.symm
  have hle : ‖(m : PadicInt p) - (n : PadicInt p)‖ ≤ (p : ℝ) ^ (-((k : ℕ) : ℤ)) := by
    have h1 : dist x y < (p : ℝ) ^ (-((k : ℕ) : ℤ)) := hxy
    rw [Subtype.dist_eq, dist_eq_norm] at h1
    rw [hm, hn]
    exact le_of_lt h1
  have hfin : dist (moritaGammaPre p x) (moritaGammaPre p y) < ε := by
    rw [hFx, hFy, dist_eq_norm]
    exact lt_of_le_of_lt (est p hp2 k m n hle) hk
  exact hfin

end MetaMathlibExt

/--
[existsUnique_moritaPadicGamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean)
-/
@[path]
private lemma existsUnique_moritaPadicGamma_eq
  {p : ℕ} [Fact p.Prime]
-- given
  (hp : p ≠ 2) :
-- imply
  ∃! Γ : C(PadicInt p, PadicInt p), IsMoritaPadicGamma p Γ := by
-- proof
  apply MetaMathlibExt.existsUnique_moritaPadicGamma p hp


-- created on 2026-10-20
-- updated on 2026-10-23
