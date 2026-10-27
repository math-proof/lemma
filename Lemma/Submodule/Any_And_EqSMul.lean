import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private lemma pow_apply_mem {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] {P : Submodule K V} {f : Module.End K V} (hf : ∀ x ∈ P, f x ∈ P) : ∀ (k : ℕ) (x : V), x ∈ P → (f ^ k) x ∈ P := by
  intro k
  induction k
  ·
    intro x hx
    simpa using hx
  ·
    rename_i k ih
    intro x hx
    rw [pow_succ', Module.End.mul_apply]
    apply hf _ (ih x hx)
private lemma pow_apply_comm {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] {f g : Module.End K V} (h : ∀ x, f (g x) = g (f x)) : ∀ (k : ℕ) (x : V), (f ^ k) (g x) = g ((f ^ k) x) := by
  intro k
  induction k
  ·
    intro x
    simp
  ·
    rename_i k ih
    intro x
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, h]
private lemma exists_common_ker {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ι : Type w} (S : ι → Module.End K V) (hS : ∀ (i j : ι) (x : V), S i (S j x) = S j (S i x)) : ∀ (n : ℕ) (U : Submodule K V), Module.finrank K U ≤ n → U ≠ ⊥ → (∀ i, ∀ x ∈ U, S i x ∈ U) → (∀ i, ∀ x ∈ U, ∃ k : ℕ, (S i ^ k) x = 0) → ∃ u ∈ U, u ≠ 0 ∧ ∀ i, S i u = 0 := by
  intro n
  induction n
  ·
    intro U hU hU0 _ _
    apply absurd (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)) hU0
  ·
    rename_i n ih
    intro U hU hU0 hstab hnil
    if hall : ∀ i, ∀ x ∈ U, S i x = 0 then
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      exact ⟨u, huU, hu0, fun i => hall i u huU⟩
    else
      obtain ⟨i₀, x₀, hx₀U, hx₀⟩ : ∃ (i : ι) (x : V), x ∈ U ∧ ¬ S i x = 0 := by simpa only [not_forall, Classical.not_imp, exists_prop] using hall
      have hx₀0 : x₀ ≠ 0 := fun h0 => hx₀ (by rw [h0, map_zero])
      have hlt : U ⊓ LinearMap.ker (S i₀) < U := by
        refine lt_of_le_of_ne inf_le_left fun h => hx₀ ?_
        have hmem : x₀ ∈ U ⊓ LinearMap.ker (S i₀) := by
          rw [h]
          apply hx₀U
        refine LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
      have hrank : Module.finrank K ↥(U ⊓ LinearMap.ker (S i₀)) ≤ n := Nat.lt_succ_iff.mp (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hlt) hU)
      have hne : U ⊓ LinearMap.ker (S i₀) ≠ ⊥ := by
        intro hbot
        obtain ⟨k, hk⟩ := hnil i₀ x₀ hx₀U
        have key : ∀ m : ℕ, (S i₀ ^ m) x₀ ∈ U ∧ ¬ (S i₀ ^ m) x₀ = 0 := by
          intro m
          induction m
          · exact ⟨by simpa using hx₀U, by simpa using hx₀0⟩
          ·
            rename_i m ihm
            refine ⟨?_, fun h0 => ihm.2 ?_⟩
            ·
              rw [pow_succ', Module.End.mul_apply]
              apply hstab i₀ _ ihm.1
            ·
              have hmem : (S i₀ ^ m) x₀ ∈ U ⊓ LinearMap.ker (S i₀) := by
                refine Submodule.mem_inf.mpr ⟨ihm.1, ?_⟩
                rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ']
                apply h0
              rw [hbot] at hmem
              apply (Submodule.mem_bot K).mp hmem
      refine (key k).2 hk
      have hstab' : ∀ i, ∀ x ∈ U ⊓ LinearMap.ker (S i₀), S i x ∈ U ⊓ LinearMap.ker (S i₀) := by
        intro i x hx
        obtain ⟨hxU, hxk⟩ := Submodule.mem_inf.mp hx
        refine Submodule.mem_inf.mpr ⟨hstab i x hxU, ?_⟩
        rw [LinearMap.mem_ker] at hxk ⊢
        rw [hS i₀ i x, hxk, map_zero]
      have hnil' : ∀ i, ∀ x ∈ U ⊓ LinearMap.ker (S i₀), ∃ k : ℕ, (S i ^ k) x = 0 := fun i x hx => hnil i x (Submodule.mem_inf.mp hx).1
      obtain ⟨u, hu, hu0, hker⟩ := ih _ hrank hne hstab' hnil'
      exact ⟨u, (Submodule.mem_inf.mp hu).1, hu0, hker⟩
/--
[Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem.lean)
-/
@[path]
private lemma main
  {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (T : ι → Module.End K V)
  (W : Submodule K V)
  (mu : ι → K)
  (v : V)
  -- given
  (hT : ∀ i j, Commute (T i) (T j))
  (hW : ∀ i, ∀ w ∈ W, T i w ∈ W)
  (hv : v ∉ W)
  (heig : ∀ i, T i v - mu i • v ∈ W) :
  -- imply
  ∃ u : V, u ≠ 0 ∧ ∀ i, T i u = mu i • u := by
  -- proof
  classical
  obtain ⟨S, hSx⟩ : ∃ S : ι → Module.End K V, ∀ (i : ι) (x : V), S i x = T i x - mu i • x := ⟨fun i => T i - mu i • 1, fun i x => by simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]⟩
  have hTx : ∀ (i j : ι) (x : V), T i (T j x) = T j (T i x) := fun i j x => by simpa only [Module.End.mul_apply] using LinearMap.congr_fun (hT i j).eq x
  have hSS : ∀ (i j : ι) (x : V), S i (S j x) = S j (S i x) := by
    intro i j x
    simp only [hSx, map_sub, map_smul, smul_sub, smul_smul, hTx i j x, mul_comm (mu i) (mu j)]
    abel
  have hWS : ∀ i, ∀ w ∈ W, S i w ∈ W := by
    intro i w hw
    rw [hSx]
    apply W.sub_mem (hW i w hw) (W.smul_mem _ hw)
  have hvS : ∀ i, S i v ∈ W := fun i => by
    rw [hSx]
    apply heig i
  have hex : ∃ d : ℕ, ∃ P : Submodule K V, Module.finrank K P = d ∧ (∀ i, ∀ x ∈ P, S i x ∈ P) ∧ ∃ p ∈ P, p ∉ W ∧ ∀ i, S i p ∈ W := ⟨_, ⊤, rfl, fun i x _ => Submodule.mem_top, v, Submodule.mem_top, hv, hvS⟩
  obtain ⟨P₀, hP₀d, hP₀S, p, hpP, hpW, hpS⟩ := Nat.find_spec hex
  have hmin : ∀ P : Submodule K V, (∀ i, ∀ x ∈ P, S i x ∈ P) → (∃ q ∈ P, q ∉ W ∧ ∀ i, S i q ∈ W) → Module.finrank K P₀ ≤ Module.finrank K P := by
    intro P h1 h2
    rw [hP₀d]
    apply Nat.find_min' hex ⟨P, rfl, h1, h2⟩
  have hP₁le : W ⊓ P₀ ⊔ Submodule.span K {p} ≤ P₀ := sup_le inf_le_right ((Submodule.span_singleton_le_iff_mem p P₀).mpr hpP)
  have hP₁S : ∀ i, ∀ x ∈ W ⊓ P₀ ⊔ Submodule.span K {p}, S i x ∈ W ⊓ P₀ := by
    intro i x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    obtain ⟨hyW, hyP⟩ := Submodule.mem_inf.mp hy
    rw [map_add, map_smul]
    apply Submodule.add_mem _ (Submodule.mem_inf.mpr ⟨hWS i y hyW, hP₀S i y hyP⟩) (Submodule.smul_mem _ c (Submodule.mem_inf.mpr ⟨hpS i, hP₀S i p hpP⟩))
  have hP₁eq : W ⊓ P₀ ⊔ Submodule.span K {p} = P₀ := Submodule.eq_of_le_of_finrank_le hP₁le (hmin _ (fun i x hx => Submodule.mem_sup_left (hP₁S i x hx)) ⟨p, Submodule.mem_sup_right (Submodule.mem_span_singleton_self p), hpW, hpS⟩)
  have hSW : ∀ i, ∀ x ∈ P₀, S i x ∈ W := by
    intro i x hx
    have hx' : x ∈ W ⊓ P₀ ⊔ Submodule.span K {p} := by
      rw [hP₁eq]
      apply hx
    refine (Submodule.mem_inf.mp (hP₁S i x hx')).1
  have hnil : ∀ i, ∀ x ∈ P₀, ∃ k : ℕ, (S i ^ k) x = 0 := by
    intro i₀ x₀ hx₀
    by_contra hcon
    simp only [not_exists] at hcon
    have hmono : Monotone (fun m => OrderDual.toDual (Submodule.map (S i₀ ^ m) P₀)) := by
      intro m m' hle x hx
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hx' : x ∈ Submodule.map (S i₀ ^ (m + k)) P₀ := hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx'
      show (S i₀ ^ (m + k)) y ∈ Submodule.map (S i₀ ^ m) P₀
      apply Submodule.mem_map.mpr ⟨(S i₀ ^ k) y, pow_apply_mem (hP₀S i₀) k y hy, by rw [pow_add, Module.End.mul_apply]⟩
    obtain ⟨n, hn : ∀ m, n ≤ m → Submodule.map (S i₀ ^ n) P₀ = Submodule.map (S i₀ ^ m) P₀⟩ := IsArtinian.monotone_stabilizes ⟨fun m => OrderDual.toDual (Submodule.map (S i₀ ^ m) P₀), hmono⟩
    have hn1 : Submodule.map (S i₀ ^ (n + 1)) P₀ = Submodule.map (S i₀ ^ (n + 1 + (n + 1))) P₀ := by rw [← hn (n + 1) (Nat.le_succ n), ← hn (n + 1 + (n + 1)) (by omega)]
    obtain ⟨y, hyP, hy⟩ : ∃ y ∈ P₀, (S i₀ ^ (n + 1 + (n + 1))) y = (S i₀ ^ (n + 1)) p := by
      have hmem : (S i₀ ^ (n + 1)) p ∈ Submodule.map (S i₀ ^ (n + 1 + (n + 1))) P₀ := by
        rw [← hn1]
        apply Submodule.mem_map_of_mem hpP
      refine Submodule.mem_map.mp hmem
    have hSny : (S i₀ ^ (n + 1)) y ∈ P₀ := pow_apply_mem (hP₀S i₀) _ y hyP
    have hSy : (S i₀ ^ (n + 1)) y ∈ W := by
      rw [pow_succ', Module.End.mul_apply]
      apply hSW i₀ _ (pow_apply_mem (hP₀S i₀) n y hyP)
    have hgood : (∀ i, ∀ x ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)), S i x ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1))) ∧ ∃ q ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)), q ∉ W ∧ ∀ i, S i q ∈ W := by
      refine ⟨fun i x hx => ?_, p - (S i₀ ^ (n + 1)) y, ?_, ?_, ?_⟩
      ·
        obtain ⟨hxP, hxk⟩ := Submodule.mem_inf.mp hx
        refine Submodule.mem_inf.mpr ⟨hP₀S i x hxP, ?_⟩
        rw [LinearMap.mem_ker] at hxk ⊢
        rw [pow_apply_comm (hSS i₀ i) (n + 1) x, hxk, map_zero]
      ·
        refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hpP hSny, ?_⟩
        rw [LinearMap.mem_ker, map_sub, ← hy, ← Module.End.mul_apply, ← pow_add, sub_self]
      ·
        intro hmem
        apply hpW (by simpa using W.add_mem hmem hSy)
      ·
        intro i
        rw [map_sub]
        apply W.sub_mem (hpS i) (hSW i _ hSny)
    have hlt : P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)) < P₀ := by
      refine lt_of_le_of_ne inf_le_left fun h => hcon (n + 1) ?_
      have hmem : x₀ ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)) := by
        rw [h]
        apply hx₀
      refine LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
    refine absurd (hmin _ hgood.1 hgood.2) (not_le.mpr (Submodule.finrank_lt_finrank_of_lt hlt))
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h
    rw [h] at hpP
    apply hpW (by rw [(Submodule.mem_bot K).mp hpP]; apply W.zero_mem)
  obtain ⟨u, -, hu0, hu⟩ := exists_common_ker S hSS (Module.finrank K P₀) P₀ le_rfl hP₀ne hP₀S hnil
  exact ⟨u, hu0, fun i => sub_eq_zero.mp ((hSx i u).symm.trans (hu i))⟩


-- created on 2026-10-20
