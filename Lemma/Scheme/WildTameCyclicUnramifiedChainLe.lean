import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false


private lemma Subgroup.sup_subgroupOf_eq_aux
  [Group G] {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
  (H ⊔ K).subgroupOf L = H.subgroupOf L ⊔ K.subgroupOf L := by
  have h1 : (H.subgroupOf L ⊔ K.subgroupOf L).map L.subtype = H ⊔ K := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hH, inf_eq_left.mpr hK]
  rw [Subgroup.subgroupOf, ← h1, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective L)]
/--
[Subgroup_exists_wild_tame_cyclic_unramified_chain_of_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subgroup_exists_wild_tame_cyclic_unramified_chain_of_le.lean)
-/
@[path]
private lemma main
  {q : ℕ} [Fact q.Prime] [Group G]
  (U W : Subgroup G) [U.Normal] [U.FiniteIndex] [W.Normal]
  (t φ : G) (S H : Subgroup G)
  -- given
  (hUW : U ≤ W)
  (hWq : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
  (hφt : (t ^ q)⁻¹ * (φ * t * φ⁻¹) ∈ W)
  (hgen : ∀ g : G, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ Subgroup.closure {t} ⊔ W)
  (hUH : U ≤ H)
  (hHS : H ≤ S)
  (hHn : (H.subgroupOf S).Normal) :
  -- imply
  ∃ P I : Subgroup G, H ≤ P ∧ P ≤ I ∧ I ≤ S ∧ (P.subgroupOf S).Normal ∧ (I.subgroupOf S).Normal ∧
    (∃ n : ℕ, (H.subgroupOf P).index = q ^ n) ∧ ¬ q ∣ (P.subgroupOf I).index ∧
    (∃ g ∈ I, ∀ s ∈ I, ∃ n : ℕ, (g ^ n)⁻¹ * s ∈ P) ∧
    (∃ g ∈ S, ∀ s ∈ S, ∃ n : ℕ, (g ^ n)⁻¹ * s ∈ I) := by
  -- proof
  classical
  let hqp : Fact q.Prime := inferInstance
  let _ : W.FiniteIndex := Subgroup.finiteIndex_of_le hUW
  let _ : Finite (G ⧸ W) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨tb, htb⟩ : ∃ tb : G ⧸ W, QuotientGroup.mk t = tb := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb : G ⧸ W, QuotientGroup.mk φ = fb := ⟨_, rfl⟩
  have hconj : fb * tb * fb⁻¹ = tb ^ q := by
    have h : (QuotientGroup.mk (t ^ q) : G ⧸ W) = QuotientGroup.mk (φ * t * φ⁻¹) := by
      rw [QuotientGroup.eq]
      refine hφt
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, htb, hfb] at h
    refine h.symm
  have hordpos : 0 < orderOf tb := orderOf_pos tb
  have hcop : Nat.Coprime q (orderOf tb) := by
    have h1 : orderOf (tb ^ q) = orderOf tb := by
      rw [← hconj]
      have : fb * tb * fb⁻¹ = MulAut.conj fb tb := (MulAut.conj_apply fb tb).symm
      rw [this]
      refine orderOf_injective (MulAut.conj fb).toMonoidHom (MulAut.conj fb).injective tb
    rw [orderOf_pow' tb hqp.out.ne_zero] at h1
    have hg : Nat.gcd (orderOf tb) q = 1 := by
      obtain h | h := (Nat.div_eq_self).mp h1
      · refine absurd h hordpos.ne'
      · refine h
    rw [Nat.coprime_comm]
    refine hg
  let Ib : Subgroup (G ⧸ W) := Subgroup.zpowers tb
  let I₀ : Subgroup G := Ib.comap (QuotientGroup.mk' W)
  have hI₀mem : ∀ g : G, g ∈ I₀ ↔ (QuotientGroup.mk g : G ⧸ W) ∈ Ib := fun _ => Iff.rfl
  have hWI₀ : W ≤ I₀ := by
    intro w hw
    rw [hI₀mem, (QuotientGroup.eq_one_iff w).mpr hw]
    refine one_mem _
  have htI₀ : t ∈ I₀ := by
    rw [hI₀mem, htb]
    refine Subgroup.mem_zpowers tb
  have hsupI₀ : Subgroup.closure {t} ⊔ W = I₀ := by
    apply le_antisymm
    ·
      rw [sup_le_iff, Subgroup.closure_le, Set.singleton_subset_iff]
      refine ⟨htI₀, hWI₀⟩
    ·
      intro g hg
      rw [hI₀mem, Subgroup.mem_zpowers_iff] at hg
      obtain ⟨k, hk⟩ := hg
      have : (QuotientGroup.mk (t ^ k) : G ⧸ W) = QuotientGroup.mk g := by
        rw [QuotientGroup.mk_zpow, htb]
        refine hk
      rw [QuotientGroup.eq] at this
      have hmem : t ^ k * ((t ^ k)⁻¹ * g) ∈ Subgroup.closure {t} ⊔ W :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_singleton t)) k))
          (Subgroup.mem_sup_right this)
      rwa [mul_inv_cancel_left] at hmem
  have hgen' : ∀ g : G, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ I₀ := fun g => by
    rw [← hsupI₀]
    refine hgen g
  have hconj_mem : ∀ x ∈ Ib, fb * x * fb⁻¹ ∈ Ib := by
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    rw [← hk]
    have : fb * tb ^ k * fb⁻¹ = (fb * tb * fb⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [this, hconj, ← zpow_natCast, ← zpow_mul]
    refine Subgroup.zpow_mem_zpowers tb _
  have hconj_mem' : ∀ x ∈ Ib, fb⁻¹ * x * fb ∈ Ib := by
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have htb : fb⁻¹ * tb * fb = tb ^ m := by
      have h1 : fb⁻¹ * (tb ^ q) * fb = tb := by
        rw [← hconj]
        group
      calc
        _ = fb⁻¹ * ((tb ^ q) ^ m) * fb := by rw [hm]
        _ = (fb⁻¹ * (tb ^ q) * fb) ^ m := by
          rw [show fb⁻¹ * (tb ^ q) ^ m * fb = MulAut.conj fb⁻¹ ((tb ^ q) ^ m) by rw [MulAut.conj_apply, inv_inv],
            map_pow, MulAut.conj_apply, inv_inv]
        _ = tb ^ m := by rw [h1]
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    rw [← hk]
    have : fb⁻¹ * tb ^ k * fb = (fb⁻¹ * tb * fb) ^ k := by
      rw [show fb⁻¹ * tb ^ k * fb = MulAut.conj fb⁻¹ (tb ^ k) by rw [MulAut.conj_apply, inv_inv], map_zpow,
        MulAut.conj_apply, inv_inv]
    rw [this, htb, ← zpow_natCast, ← zpow_mul]
    refine Subgroup.zpow_mem_zpowers tb _
  have hconj_pow : ∀ (n : ℕ) (y : G ⧸ W), y ∈ Ib → fb ^ n * y * (fb ^ n)⁻¹ ∈ Ib := by
    intro n
    induction n
    ·
      intro y hy
      simp
      refine hy
    ·
      rename_i n ih
      intro y hy
      have h := hconj_mem _ (ih y hy)
      have heq : fb ^ (n + 1) * y * (fb ^ (n + 1))⁻¹ = fb * (fb ^ n * y * (fb ^ n)⁻¹) * fb⁻¹ := by
        rw [pow_succ']
        group
      rw [heq]
      refine h
  let hIbN : Ib.Normal := by
    refine ⟨fun y hy g => ?_⟩
    induction g using QuotientGroup.induction_on
    rename_i g0
    obtain ⟨n, hn⟩ := hgen' g0
    rw [hI₀mem] at hn
    obtain ⟨x, hxdef⟩ : ∃ x : G ⧸ W, QuotientGroup.mk ((φ ^ n)⁻¹ * g0) = x := ⟨_, rfl⟩
    rw [hxdef] at hn
    have hg0 : (QuotientGroup.mk g0 : G ⧸ W) = fb ^ n * x := by
      rw [← hxdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hfb]
      group
    have hxy : x * y * x⁻¹ = y := by
      rw [Subgroup.mem_zpowers_iff] at hn hy
      obtain ⟨a, ha⟩ := hn
      obtain ⟨b, hb⟩ := hy
      rw [← ha, ← hb]
      group
    rw [hg0, show fb ^ n * x * y * (fb ^ n * x)⁻¹ = fb ^ n * (x * y * x⁻¹) * (fb ^ n)⁻¹ by group, hxy]
    refine hconj_pow n y hy
  let hI₀N : I₀.Normal := Subgroup.Normal.comap hIbN _
  have hcardIb : Nat.card Ib = orderOf tb := Nat.card_zpowers tb
  have hrelWI₀ : W.relIndex I₀ = orderOf tb := by
    rw [← hcardIb]
    let f : I₀ →* (G ⧸ W) := (QuotientGroup.mk' W).comp I₀.subtype
    have hker : f.ker = W.subgroupOf I₀ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      refine QuotientGroup.eq_one_iff (x : G)
    have hrange : f.range = Ib := by
      ext y
      constructor
      ·
        intro hy
        obtain ⟨x, hx⟩ := hy
        rw [← hx]
        refine (hI₀mem x).mp x.2
      ·
        intro hy
        induction y using QuotientGroup.induction_on
        rename_i g
        refine ⟨⟨g, (hI₀mem g).mpr hy⟩, rfl⟩
    rw [Subgroup.relIndex, ← hker, ← hrange]
    refine Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hnormP : ((H ⊔ (W ⊓ S)).subgroupOf S).Normal := by
    rw [Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right]
    let _ := hHn
    let _ : (W.subgroupOf S).Normal := inferInstance
    infer_instance
  have hnormI : ((H ⊔ (I₀ ⊓ S)).subgroupOf S).Normal := by
    rw [Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right]
    let _ := hHn
    let _ : (I₀.subgroupOf S).Normal := inferInstance
    infer_instance
  have hreldvd : ∀ (L' L : Subgroup G), L' ≤ L → W.relIndex L' ∣ W.relIndex L := by
    intro L' L hle
    let f : (L' ⧸ W.subgroupOf L') →* (L ⧸ W.subgroupOf L) :=
      QuotientGroup.map _ _ (Subgroup.inclusion hle) (fun x hx => by
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
        refine hx)
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      induction x using QuotientGroup.induction_on
      rename_i y
      rw [MonoidHom.mem_ker] at hx
      change (QuotientGroup.mk (Subgroup.inclusion hle y) : L ⧸ W.subgroupOf L) = 1 at hx
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine hx
    refine Subgroup.card_dvd_of_injective f hf
  refine ⟨H ⊔ (W ⊓ S), H ⊔ (I₀ ⊓ S), le_sup_left, sup_le_sup_left (inf_le_inf_right S hWI₀) H,
    sup_le hHS inf_le_right, hnormP, hnormI, ?_, ?_, ?_, ?_⟩
  ·
    let _ := hHn
    have h1 : (H.subgroupOf (H ⊔ (W ⊓ S))).index = (H.subgroupOf S).relIndex (W.subgroupOf S) := by
      rw [← Subgroup.relIndex, ← Subgroup.relIndex_subgroupOf (sup_le hHS inf_le_right : H ⊔ (W ⊓ S) ≤ S),
        Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right, Subgroup.relIndex_sup_left]
    have hUH' : U.subgroupOf S ≤ H.subgroupOf S := fun x hx => hUH hx
    have h2 : (H.subgroupOf S).relIndex (W.subgroupOf S) ∣ (U.subgroupOf S).relIndex (W.subgroupOf S) :=
      Subgroup.relIndex_dvd_of_le_left _ hUH'
    let _ : ((U.subgroupOf S).subgroupOf (W.subgroupOf S)).FiniteIndex := inferInstance
    let _ : Finite ((W.subgroupOf S) ⧸ (U.subgroupOf S).subgroupOf (W.subgroupOf S)) :=
      Subgroup.finite_quotient_of_finiteIndex
    have hPG : IsPGroup q ((W.subgroupOf S) ⧸ (U.subgroupOf S).subgroupOf (W.subgroupOf S)) := by
      intro x
      induction x using QuotientGroup.induction_on
      rename_i w
      obtain ⟨a, ha⟩ := hWq ((w : S) : G) w.2
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      refine ha
    obtain ⟨n, hn⟩ := hPG.exists_card_eq
    have h3 : (U.subgroupOf S).relIndex (W.subgroupOf S) = q ^ n := hn
    rw [h1]
    rw [h3] at h2
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hqp.out).mp h2
    refine ⟨m, hm⟩
  ·
    let _ := hHn
    let _ : ((H ⊔ (W ⊓ S)).subgroupOf S).Normal := hnormP
    have hWS_le : W.subgroupOf S ≤ (H ⊔ (W ⊓ S)).subgroupOf S := by
      rw [Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right]
      refine le_sup_right
    have h1 : ((H ⊔ (W ⊓ S)).subgroupOf (H ⊔ (I₀ ⊓ S))).index =
        ((H ⊔ (W ⊓ S)).subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S) := by
      rw [← Subgroup.relIndex, ← Subgroup.relIndex_subgroupOf (sup_le hHS inf_le_right : H ⊔ (I₀ ⊓ S) ≤ S),
        Subgroup.sup_subgroupOf_eq_aux hHS (inf_le_right : I₀ ⊓ S ≤ S),
        Subgroup.sup_subgroupOf_eq_aux hHS (inf_le_right : W ⊓ S ≤ S)]
      let _ : (H.subgroupOf S ⊔ (W ⊓ S).subgroupOf S).Normal := by
        rw [← Subgroup.sup_subgroupOf_eq_aux hHS (inf_le_right : W ⊓ S ≤ S)]
        refine hnormP
      have : H.subgroupOf S ⊔ (I₀ ⊓ S).subgroupOf S =
          (H.subgroupOf S ⊔ (W ⊓ S).subgroupOf S) ⊔ (I₀ ⊓ S).subgroupOf S := by
        rw [sup_assoc]
        congr 1
        rw [Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right, eq_comm, sup_eq_right]
        refine fun x hx => hWI₀ hx
      rw [this, Subgroup.relIndex_sup_left]
    have h2 : ((H ⊔ (W ⊓ S)).subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S)
      ∣ (W.subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S) := Subgroup.relIndex_dvd_of_le_left _ hWS_le
    have h3 : (W.subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S) = W.relIndex (I₀ ⊓ S) :=
      Subgroup.relIndex_subgroupOf inf_le_right
    have h4 : W.relIndex (I₀ ⊓ S) ∣ W.relIndex I₀ := hreldvd _ _ inf_le_left
    rw [h1]
    intro hdvd
    have : q ∣ orderOf tb := by
      rw [← hrelWI₀]
      refine hdvd.trans (h2.trans (h3 ▸ h4))
    refine (Nat.Prime.coprime_iff_not_dvd hqp.out).mp hcop this
  ·
    let _ : Finite (G ⧸ W) := inferInstance
    let ρ : G →* G ⧸ W := QuotientGroup.mk' W
    have hρ : ∀ g, ρ g = 1 ↔ g ∈ W := fun g => QuotientGroup.eq_one_iff g
    have hρI₀ : ∀ g, g ∈ I₀ ↔ ρ g ∈ Ib := fun g => hI₀mem g
    let _ : IsCyclic Ib := ⟨⟨⟨tb, Subgroup.mem_zpowers tb⟩, fun y => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
      refine ⟨k, Subtype.ext ?_⟩
      rw [← hk]
      rfl⟩⟩⟩
    let J : Subgroup Ib := ((I₀ ⊓ S).map ρ).subgroupOf Ib
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := J)
    obtain ⟨g₁, hg₁, hg₁γ⟩ : ∃ g₁ ∈ I₀ ⊓ S, ρ g₁ = ((γ : Ib) : G ⧸ W) := by
      obtain ⟨g₁, hg₁, e⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp γ.2)
      refine ⟨g₁, hg₁, e⟩
    refine ⟨g₁, Subgroup.mem_sup_right hg₁, fun s hs => ?_⟩
    have hsS : s ∈ S := (sup_le hHS inf_le_right : H ⊔ (I₀ ⊓ S) ≤ S) hs
    let _ := hHn
    have hs' : (⟨s, hsS⟩ : S) ∈ H.subgroupOf S ⊔ (I₀ ⊓ S).subgroupOf S := by
      rw [← Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.mem_subgroupOf]
      refine hs
    have hs'' : ((⟨s, hsS⟩ : S) : S) ∈ ((H.subgroupOf S ⊔ (I₀ ⊓ S).subgroupOf S : Subgroup S) : Set S) := hs'
    rw [Subgroup.normal_mul] at hs''
    obtain ⟨h, hh, i, hi, hhi⟩ := Set.mem_mul.mp hs''
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hh hi
    have hiJ : (⟨ρ (i : G), (hρI₀ _).mp hi.1⟩ : Ib) ∈ J :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨i, hi, rfl⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨_, hiJ⟩)
    have hk' : (ρ g₁) ^ k = ρ (i : G) := by
      have := congrArg (fun x : J => ((x : Ib) : G ⧸ W)) hk
      simpa [hg₁γ] using this
    have hk'' : (ρ g₁) ^ (k % (orderOf (ρ g₁) : ℤ)).toNat = ρ (i : G) := by
      rw [← hk', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (orderOf_pos _).ne')),
        zpow_mod_orderOf]
    refine ⟨(k % (orderOf (ρ g₁) : ℤ)).toNat, ?_⟩
    have hg₁S : g₁ ∈ S := hg₁.2
    have hmemW : (g₁ ^ (k % (orderOf (ρ g₁) : ℤ)).toNat)⁻¹ * (i : G) ∈ W := by
      rw [← hρ, map_mul, map_inv, map_pow, hk'', inv_mul_cancel]
    have hsplit : (g₁ ^ (k % (orderOf (ρ g₁) : ℤ)).toNat)⁻¹ * s =
        ((g₁ ^ (k % (orderOf (ρ g₁) : ℤ)).toNat)⁻¹ * (h : G) * g₁ ^ (k % (orderOf (ρ g₁) : ℤ)).toNat) *
          ((g₁ ^ (k % (orderOf (ρ g₁) : ℤ)).toNat)⁻¹ * (i : G)) := by
      rw [← show ((h : G)) * (i : G) = s from congrArg Subtype.val hhi]
      group
    rw [hsplit]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ⟨hmemW,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hg₁S _)) hi.2⟩)
    have hconjH : ∀ (x : G), x ∈ S → ∀ y ∈ H, x⁻¹ * y * x ∈ H := by
      intro x hx y hy
      have := hHn.conj_mem ⟨y, hHS hy⟩ (Subgroup.mem_subgroupOf.mpr hy) (⟨x, hx⟩⁻¹)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    refine hconjH _ (Subgroup.pow_mem _ hg₁S _) _ hh
  ·
    let _ : Finite (G ⧸ I₀) := by
      let _ : I₀.FiniteIndex := Subgroup.finiteIndex_of_le hWI₀
      refine Subgroup.finite_quotient_of_finiteIndex
    let π : G →* G ⧸ I₀ := QuotientGroup.mk' I₀
    have hπ : ∀ g, π g = 1 ↔ g ∈ I₀ := fun g => QuotientGroup.eq_one_iff g
    let _ : IsCyclic (G ⧸ I₀) := by
      refine ⟨⟨π φ, fun x => ?_⟩⟩
      induction x using QuotientGroup.induction_on
      rename_i g
      obtain ⟨n, hn⟩ := hgen' g
      refine ⟨n, ?_⟩
      show (π φ) ^ (n : ℤ) = π g
      rw [zpow_natCast, ← map_pow]
      have : π ((φ ^ n)⁻¹ * g) = 1 := (hπ _).mpr hn
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      refine this
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := S.map π)
    obtain ⟨g₀, hg₀S, hg₀⟩ := Subgroup.mem_map.mp γ.2
    refine ⟨g₀, hg₀S, fun s hs => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨π s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩⟩)
    have hk' : (π g₀) ^ k = π s := by
      have := congrArg Subtype.val hk
      simpa [hg₀] using this
    have hk'' : (π g₀) ^ (k % (orderOf (π g₀) : ℤ)).toNat = π s := by
      rw [← hk', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (orderOf_pos _).ne')),
        zpow_mod_orderOf]
    refine ⟨(k % (orderOf (π g₀) : ℤ)).toNat, ?_⟩
    have hmemI₀ : (g₀ ^ (k % (orderOf (π g₀) : ℤ)).toNat)⁻¹ * s ∈ I₀ := by
      rw [← hπ, map_mul, map_inv, map_pow, hk'', inv_mul_cancel]
    refine Subgroup.mem_sup_right ⟨hmemI₀, Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hg₀S _)) hs⟩


-- created on 2026-10-20
