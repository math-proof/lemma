import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Enumerative.IdentityProductNecklace.Part4
open MetaMathlibExt


namespace MetaMathlibExt

/--
[orbSet_mem_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma orbSet_mem_self (G : Type*) [Group G]
  (n : ℕ) [NeZero n]
  (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
  x.val ∈ orbSet G n x.val := by
  refine ⟨0, NeZero.pos n, fun i => ?_⟩
  have hval : (i.val + 0) % n = i.val := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  change x.val i = x.val ⟨(i.val + 0) % n, _⟩
  exact congrArg x.val (Fin.ext hval.symm)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[neckQuot_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma neckQuot_injective (G : Type*) [Group G]
  (n : ℕ) [NeZero n] : Function.Injective (neckQuot G n) := by
  intro q1 q2 hq
  have hq' : orbSet G n (Quotient.out q1).val
    = orbSet G n (Quotient.out q2).val := hq
  have hmem : (Quotient.out q2).val ∈ orbSet G n (Quotient.out q1).val := by
    have hself := orbSet_mem_self G n (Quotient.out q2)
    rwa [← hq'] at hself
  obtain ⟨m, hmn, hm⟩ := hmem
  have hkval : ((m : ZMod n)).val = m := ZMod.val_natCast_of_lt hmn
  have hact : ((m : ZMod n) +ᵥ (Quotient.out q1)) = Quotient.out q2 := by
    apply Subtype.ext
    funext i
    show ((m : ZMod n) +ᵥ Quotient.out q1).val i = (Quotient.out q2).val i
    have hL : ((m : ZMod n) +ᵥ (Quotient.out q1)).val i
      = (Quotient.out q1).val ⟨(i.val + m) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
      change (Quotient.out q1).val ⟨(i.val + ((m : ZMod n)).val) % n, _⟩ = _
      have hvaleq : (i.val + ((m : ZMod n)).val) % n = (i.val + m) % n := by
        rw [hkval]
      exact congrArg (Quotient.out q1).val (Fin.ext hvaleq)
    rw [hL]
    exact (hm i).symm
  have hrel : (AddAction.orbitRel (ZMod n)
    {x : Fin n → G // (List.ofFn x).prod = 1}).r
    (Quotient.out q2) (Quotient.out q1) :=
    AddAction.mem_orbit_iff.mpr ⟨(m : ZMod n), hact⟩
  have hqq : (⟦Quotient.out q1⟧ : Quotient _) = ⟦Quotient.out q2⟧ :=
    (Quot.sound hrel).symm
  have e1 : q1 = (⟦Quotient.out q1⟧ : Quotient _) := (Quotient.out_eq q1).symm
  have e2 : q2 = (⟦Quotient.out q2⟧ : Quotient _) := (Quotient.out_eq q2).symm
  rwa [e1, e2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[addOrderOf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma addOrderOf_eq (n : ℕ) [NeZero n] (k : ZMod n) :
  addOrderOf k = n / Nat.gcd n k.val := by
  have hnpos : 0 < n := NeZero.pos n
  have hddpos : 0 < Nat.gcd n k.val := Nat.gcd_pos_of_pos_left _ hnpos
  have hcop0 := Nat.coprime_div_gcd_div_gcd hddpos (m := n) (n := k.val)
  obtain ⟨nv, hnv⟩ := Nat.gcd_dvd_left n k.val
  obtain ⟨kv, hkv⟩ := Nat.gcd_dvd_right n k.val
  set G := Nat.gcd n k.val with hG
  have hnv_eq : n / G = nv := by
    have hmul : G * nv / G = nv := by
      rw [mul_comm G nv]
      exact Nat.mul_div_cancel _ hddpos
    rwa [← hnv] at hmul
  have hkv_eq : k.val / G = kv := by
    have hmul : G * kv / G = kv := by
      rw [mul_comm G kv]
      exact Nat.mul_div_cancel _ hddpos
    rwa [← hkv] at hmul
  have hcop : Nat.Coprime nv kv := by
    rwa [hnv_eq, hkv_eq] at hcop0
  rw [hnv_eq]
  apply Nat.dvd_antisymm
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    have hcast : nv • k = (((nv * k.val : ℕ)) : ZMod n) := by
      rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.natCast_eq_zero_iff]
    have e1 : nv * k.val = nv * (G * kv) := by rw [hkv]
    have e2 : nv * (G * kv) = (G * nv) * kv := by ring
    have e3 : (G * nv) * kv = n * kv := by rw [← hnv]
    exact ⟨kv, by rw [e1, e2, e3]⟩
  · set t := addOrderOf k with ht
    have h0 : t • k = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp dvd_rfl
    have hcast : t • k
      = (((t * k.val : ℕ)) : ZMod n) := by
      rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
    have h0' : n ∣ t * k.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      rwa [hcast] at h0
    rw [hkv, hnv] at h0'
    have h1 : nv ∣ t * kv := by
      have hring : t * (G * kv)
        = G * (t * kv) := by ring
      rw [hring] at h0'
      exact (Nat.mul_dvd_mul_iff_left hddpos).mp h0'
    exact hcop.dvd_of_dvd_mul_right h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prod_update_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma prod_update_last (G : Type*) [Group G]
  (d : ℕ) (hd : 0 < d) (a : Fin d → G) (t : G) :
  (List.ofFn (Function.update a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
    (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))).prod
  = (List.ofFn a).prod * t := by
  have htake_len : ((List.ofFn a).take (d - 1)).length = d - 1 := by
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.sub_le _ _)]
  have key : ∀ v : G, List.ofFn
    (Function.update a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ v)
    = (List.ofFn a).take (d - 1) ++ [v] := by
    intro v
    refine List.ext_getElem ?_ ?_
    · rw [List.length_ofFn, List.length_append, List.length_take,
      List.length_ofFn, List.length_singleton,
      Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_add_cancel hd]
    · intro j h1 h2
      by_cases hj : j < d - 1
      · have hj' : j < ((List.ofFn a).take (d - 1)).length := by omega
        have hne : (⟨j, by omega⟩ : Fin d)
          ≠ ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ := by
          intro hcon
          have hvv : j = d - 1 := Fin.ext_iff.mp hcon
          omega
        rw [List.getElem_append_left hj', List.getElem_take, List.getElem_ofFn,
          List.getElem_ofFn, Function.update_of_ne hne]
      · have hlen2 : ((List.ofFn a).take (d - 1) ++ [v]).length = d := by
        rw [List.length_append, List.length_take, List.length_ofFn,
          List.length_singleton, Nat.min_eq_left (Nat.sub_le _ _),
          Nat.sub_add_cancel hd]
        have hjd : j = d - 1 := by
          have hjd' : j < d := by simpa [hlen2] using h2
          omega
        subst hjd
        have hle : ((List.ofFn a).take (d - 1)).length ≤ d - 1 := by omega
        rw [List.getElem_ofFn, Function.update_self,
          List.getElem_append_right hle, List.getElem_singleton]
  have e1 := key (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t)
  have e2 := key (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩)
  have e3 : Function.update a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
    (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩) = a :=
    Function.update_eq_self _ _
  rw [e3] at e2
  rw [e1, List.prod_append, List.prod_singleton]
  conv_rhs => rw [e2, List.prod_append, List.prod_singleton]
  rw [mul_assoc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fiber_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma fiber_card_eq (G : Type*) [Group G] [Fintype G] [DecidableEq G]
  (d : ℕ) (hd : 0 < d) (g₀ : G) :
  Fintype.card {a : Fin d → G // (List.ofFn a).prod = g₀}
  = Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1} := by
  classical
  refine Fintype.card_congr ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  · exact fun a => ⟨Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
    (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹), by
    rw [prod_update_last G d hd a.val g₀⁻¹, a.prop, mul_inv_cancel]⟩
  · exact fun b => ⟨Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
    (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀), by
    rw [prod_update_last G d hd b.val g₀, b.prop, one_mul]⟩
  · intro a
    apply Subtype.ext
    change Function.update (Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      ((Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀) = a.val
    have hv1 : (Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      = a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹ :=
      Function.update_self _ _ _
    rw [hv1]
    have hval : (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹) * g₀
      = a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [hval, Function.update_idem]
    exact Function.update_eq_self _ _
  · intro b
    apply Subtype.ext
    change Function.update (Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      ((Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹) = b.val
    have hv2 : (Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      = b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀ :=
      Function.update_self _ _ _
    rw [hv2]
    have hval : (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀) * g₀⁻¹
      = b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ :=
      mul_inv_cancel_right _ _
    rw [hval, Function.update_idem]
    exact Function.update_eq_self _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fiber_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma fiber_count (G : Type*) [Group G] [Fintype G] [DecidableEq G]
  (d e : ℕ) (hd : 0 < d) :
  Fintype.card {a : Fin d → G // ((List.ofFn a).prod) ^ e = 1}
  = (Fintype.card G) ^ (d - 1) * Fintype.card {g : G // g ^ e = 1} := by
  classical
  have hCpos : 0 < Fintype.card G := Fintype.card_pos
  have hfib1 : Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1}
    = (Fintype.card G) ^ (d - 1) := by
    have hmem : ∀ b : Fin d → G, (List.ofFn (Function.update b
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))).prod
      = 1 := by
      intro b
      rw [prod_update_last G d hd b ((List.ofFn b).prod)⁻¹, mul_inv_cancel]
    have hEquiv : ({a : Fin d → G // (List.ofFn a).prod = 1} × G)
      ≃ (Fin d → G) := by
      refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
      · exact fun p => Function.update p.1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
        (p.1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * p.2)
      · exact fun b => (⟨Function.update b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
        (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹),
        hmem b⟩, (List.ofFn b).prod)
      · intro a
        obtain ⟨a1, t⟩ := a
        have hpi : (List.ofFn (Function.update a1.val
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))).prod = t := by
          rw [prod_update_last G d hd a1.val t, a1.prop, one_mul]
        have hfst : Function.update (Function.update a1.val
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (((Function.update a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩) *
          ((List.ofFn (Function.update a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))).prod)⁻¹)
          = a1.val := by
          rw [Function.update_self, hpi]
          have hv3 : (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t) * t⁻¹
            = a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ :=
            mul_inv_cancel_right _ _
          rw [hv3, Function.update_idem]
          exact Function.update_eq_self _ _
        rw [Prod.ext_iff]
        exact ⟨Subtype.ext hfst, hpi⟩
      · intro b
        change Function.update (Function.update b
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          ((Function.update b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * (List.ofFn b).prod) = b
        have hv1 : (Function.update b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))
          ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          = b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹ :=
          Function.update_self _ _ _
        rw [hv1]
        have hv2 : (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹)
          * (List.ofFn b).prod = b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
        rw [hv2, Function.update_idem]
        exact Function.update_eq_self _ _
    have hcard := Fintype.card_congr hEquiv
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hcard
    have hCd : (Fintype.card G) ^ d
      = (Fintype.card G) ^ (d - 1) * Fintype.card G := by
      conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
    rw [hCd] at hcard
    exact mul_right_cancel₀ (ne_of_gt hCpos) hcard
  have hmaps : Set.MapsTo (fun a : Fin d → G => (List.ofFn a).prod)
    ↑(Finset.univ.filter
      (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1))
    ↑(Finset.univ.filter (fun g : G => g ^ e = 1)) := by
    intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ,
      true_and] at ha ⊢
    exact ha
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter
      (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1))
    (t := Finset.univ.filter (fun g : G => g ^ e = 1))
    (f := fun a : Fin d → G => (List.ofFn a).prod) hmaps
  have hfib : ∀ g ∈ Finset.univ.filter (fun g : G => g ^ e = 1),
    {a ∈ Finset.univ.filter
      (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)
      | (List.ofFn a).prod = g}.card
    = Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1} := by
    intro g hg
    have hg1 : g ^ e = 1 := by
      have hgg := hg
      simpa [Finset.mem_filter] using hgg
    have hseq : {a ∈ Finset.univ.filter
      (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)
      | (List.ofFn a).prod = g}
      = Finset.univ.filter (fun a : Fin d → G => (List.ofFn a).prod = g) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rwa [h]
    have hce : Fintype.card {a : Fin d → G // (List.ofFn a).prod = g}
      = (Finset.univ.filter
        (fun a : Fin d → G => (List.ofFn a).prod = g)).card :=
      Fintype.card_ofFinset _ (fun a => by
        constructor
        · intro h
          exact (Finset.mem_filter.mp h).2
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hseq, ← hce]
    exact fiber_card_eq G d hd g
  have htot : (Finset.univ.filter
    (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)).card
    = (Finset.univ.filter (fun g : G => g ^ e = 1)).card
      * Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1} := by
    rw [hsum, Finset.sum_congr rfl (fun g hg => hfib g hg), Finset.sum_const]
    simp only [nsmul_eq_mul, Nat.cast_id]
  have hLHS : Fintype.card {a : Fin d → G // ((List.ofFn a).prod) ^ e = 1}
    = (Finset.univ.filter
      (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)).card :=
    Fintype.card_ofFinset _ (fun a => by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hRHS : (Finset.univ.filter (fun g : G => g ^ e = 1)).card
    = Fintype.card {g : G // g ^ e = 1} :=
    (Fintype.card_ofFinset (p := {g : G | g ^ e = 1}) _ (fun g => by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).symm
  rw [hLHS, htot, hfib1, hRHS, mul_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_fixedBy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma card_fixedBy (G : Type*) [Group G] [Fintype G] [DecidableEq G]
  (n : ℕ) [NeZero n] (k : ZMod n) :
  Fintype.card ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k)
  = (Fintype.card G) ^ (n / addOrderOf k - 1)
    * Fintype.card {g : G // g ^ addOrderOf k = 1} := by
  classical
  have he : addOrderOf k = n / Nat.gcd n k.val := addOrderOf_eq n k
  have hddvd_n : Nat.gcd n k.val ∣ n := Nat.gcd_dvd_left _ _
  have hn0 : n ≠ 0 := (NeZero.pos n).ne'
  have hde : n / addOrderOf k = Nat.gcd n k.val := by
    rw [he, Nat.div_div_self hddvd_n hn0]
  rw [hde, he, Fintype.card_congr (fixedBy_equiv_gcd G n k)]
  exact fiber_count G _ _ (Nat.gcd_pos_of_pos_left _ (NeZero.pos n))

end MetaMathlibExt

/--
[identity_product_necklace_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean)
-/
@[path]
private lemma identity_product_necklace_count_eq
  [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (Set.ncard
    { O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧ O =
    { y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ hn⟩ } } : ℚ) =
    (1 / (n : ℚ)) * Finset.sum (Nat.divisors n)
    (fun d => (Nat.totient (n / d) : ℚ) * (Fintype.card { g : G // g ^ (n / d) = 1 } : ℚ) *
    ((Fintype.card G : ℚ) ^ (d - 1))) := by
-- proof
  apply MetaMathlibExt.identity_product_necklace_count G n hn


-- created on 2026-10-20
-- updated on 2026-10-23
