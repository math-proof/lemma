import Mathlib
import sympy.Basic

open LinearMap
open Submodule
open AdicCompletion

/--
[AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant.lean)
-/

private noncomputable def mapExactAuxDelta
  {R : Type*}
  [CommRing R]
  (I : Ideal R)
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {N : Type*}
  [AddCommGroup N]
  [Module R N]
  [IsNoetherianRing R]
  [Module.Finite R N]
  {f : M →ₗ[R] N}
  (hf : Function.Injective f)
  {k : ℕ}
  (hkn : ∀ n ≥ k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
  (x : AdicCauchySequence I N)
  {n : ℕ} {d : N}
  (hdmem : d ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N)) {y yₙ : M}
  (hd : f y = x (k + n + 1) - d) (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N)) :
  { d : (I ^ n • ⊤ : Submodule R M)
    | f (yₙ + d) - x (k + n + 1) ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N) } :=
have h : f (y - yₙ) ∈ (I ^ (k + n) • ⊤ : Submodule R N) := by
  simp only [map_sub, hd]
  convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) ∈ I ^ (k + n) • ⊤
  · abel
  · refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) hyₙ
    · rw [← Submodule.Quotient.eq]
      exact AdicCauchySequence.mk_eq_mk (by lia) _
    · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hdmem
have hincl : I ^ (k + n - k) • (I ^ k • ⊤ ⊓ range f) ≤ I ^ (k + n - k) • (range f) :=
  smul_mono_right _ inf_le_right
have hyyₙ : y - yₙ ∈ (I ^ n • ⊤ : Submodule R M) := by
  convert_to y - yₙ ∈ (I ^ (k + n - k) • ⊤ : Submodule R M)
  · simp
  · rw [← Submodule.comap_map_eq_of_injective hf (I ^ (k + n - k) • ⊤ : Submodule R M),
      Submodule.map_smul'', Submodule.map_top]
    apply hincl
    rw [← hkn (k + n) (by lia)]
    exact ⟨h, ⟨y - yₙ, rfl⟩⟩
⟨⟨y - yₙ, hyyₙ⟩, by simpa [hd, Nat.succ_eq_add_one, Nat.add_assoc]⟩

private noncomputable def mapExactAux
  {R : Type*}
  [CommRing R]
  (I : Ideal R)
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {N : Type*}
  [AddCommGroup N]
  [Module R N]
  {P : Type*}
  [AddCommGroup P]
  [Module R P]
  [IsNoetherianRing R]
  [Module.Finite R N]
  {f : M →ₗ[R] N}
  {g : N →ₗ[R] P}
  (hf : Function.Injective f)
  (hfg : Function.Exact f g)
  (hg : Function.Surjective g)
  {k : ℕ}
  (hkn : ∀ n ≥ k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
  (x : AdicCauchySequence I N)
  (hker : ∀ (n : ℕ), g (x n) ∈ (I ^ n • ⊤ : Submodule R P))
  :
  (n : ℕ) → { a : M | f a - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N) }
| .zero =>
  let d := (h2 0).choose
  let y := (h2 0).choose_spec.choose
  have hdy : f y = x (k + 0) - d := (h2 0).choose_spec.choose_spec.right
  have hdmem : d ∈ (I ^ (k + 0) • ⊤ : Submodule R N) := (h2 0).choose_spec.choose_spec.left
  ⟨y, by simpa [hdy]⟩
| .succ n =>
  let d := (h2 <| n + 1).choose
  let y := (h2 <| n + 1).choose_spec.choose
  have hdy : f y = x (k + (n + 1)) - d := (h2 <| n + 1).choose_spec.choose_spec.right
  have hdmem : d ∈ (I ^ (k + (n + 1)) • ⊤ : Submodule R N) :=
    (h2 <| n + 1).choose_spec.choose_spec.left
  let ⟨yₙ, (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N))⟩ :=
    mapExactAux I hf hfg hg hkn x hker n
  let ⟨d, hd⟩ := mapExactAuxDelta I hf hkn x hdmem hdy hyₙ
  ⟨yₙ + d, hd⟩
where
h1 (n : ℕ) : g (x (k + n)) ∈ Submodule.map g (I ^ (k + n) • ⊤ : Submodule R N) := by
  rw [map_smul'', Submodule.map_top, range_eq_top.mpr hg]
  exact hker (k + n)
h2 (n : ℕ) : ∃ (d : N) (y : M),
    d ∈ (I ^ (k + n) • ⊤ : Submodule R N) ∧ f y = x (k + n) - d := by
  obtain ⟨d, hdmem, hd⟩ := h1 n
  obtain ⟨y, hdy⟩ := (hfg (x (k + n) - d)).mp (by simp [hd])
  exact ⟨d, y, hdmem, hdy⟩


private lemma  map_injective'
  {R : Type*}
  [CommRing R]
  (I : Ideal R)
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {N : Type*}
  [AddCommGroup N]
  [Module R N]
  [IsNoetherianRing R] [Module.Finite R N] {f : M →ₗ[R] N}
  (hf : Function.Injective f) : Function.Injective (map I f) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a ↦ ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨42, fun n _ ↦ ⟨n + k, by lia, n, by lia, ?_⟩⟩
  rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M),
    Submodule.map_smul'', Submodule.map_top]
  apply (smul_mono_right _ inf_le_right : I ^ n • (I ^ k • ⊤ ⊓ (range f)) ≤ _)
  nth_rw 1 [show n = n + k - k by lia]
  rw [← hk (n + k) (show n + k ≥ k by lia)]
  exact ⟨by simpa using congrArg (fun x ↦ x.val (n + k)) hx, ⟨a (n + k), rfl⟩⟩


private lemma  map_exact'
  {R : Type*}
  [CommRing R]
  (I : Ideal R)
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {N : Type*}
  [AddCommGroup N]
  [Module R N]
  {P : Type*}
  [AddCommGroup P]
  [Module R P]
  [IsNoetherianRing R]
  [Module.Finite R N]
  {f : M →ₗ[R] N}
  {g : N →ₗ[R] P}
  (hf : Function.Injective f)
  (hfg : Function.Exact f g)
  (hg : Function.Surjective g)
  : Function.Exact (map I f) (map I g) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y ↦ ?_)
  · rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  ·
    apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
    intro hz
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
    have hb (n : ℕ) : g (b n) ∈ (I ^ n • ⊤ : Submodule R P) := by
      simpa using congrArg (fun x ↦ x.val n) hz
    let a := mapExactAux I hf hfg hg hk b hb
    refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n ↦ (a n : M)) ?_), ?_⟩
    · refine fun n ↦ SModEq.symm ?_
      simp [a, mapExactAux, SModEq]
    ·
      ext n
      suffices h : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
            Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (k + n)) by
        simp [h, AdicCauchySequence.mk_eq_mk (show n ≤ k + n by lia)]
      rw [Submodule.Quotient.eq]
      exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) (a n).property

private lemma  map_sub_apply
  {R : Type*}
  [CommRing R]
  (I : Ideal R)
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {N : Type*}
  [AddCommGroup N]
  [Module R N]
  (f g : M →ₗ[R] N) (x : AdicCompletion I M) :
  map I (f - g) x = map I f x - map I g x := by
  apply AdicCompletion.induction_on I M x (fun a ↦ ?_)
  ext n
  simp




open _root_.AdicCompletion in
@[path]
private lemma main
  [CommRing A] [IsNoetherianRing A] [CommRing S] [Algebra A S] [Module.Finite A S] [FaithfulSMul A S] [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S] [Algebra.IsInvariant A S G]
  {I : Ideal A} :
-- imply
  Function.Injective (AdicCompletion.map I (Algebra.linearMap A S)) ∧
    ∀ x : AdicCompletion I S,
      x ∈ LinearMap.range (AdicCompletion.map I (Algebra.linearMap A S)) ↔
        ∀ g : G, AdicCompletion.map I (DistribSMul.toLinearMap A S g) x = x := by
-- proof
  classical
    have : Fintype G := Fintype.ofFinite G

    have hι : Function.Injective (Algebra.linearMap A S) := FaithfulSMul.algebraMap_injective A S

    have hfix : ∀ g : G, DistribSMul.toLinearMap A S g ∘ₗ Algebra.linearMap A S =
        Algebra.linearMap A S := fun g ↦ by
      ext
      simp

    let δ : S →ₗ[A] (G → S) := LinearMap.pi fun g ↦ DistribSMul.toLinearMap A S g - LinearMap.id
    have hδ_apply : ∀ (s : S) (g : G), δ s g = g • s - s := fun s g ↦ rfl
    have hproj : ∀ g : G, LinearMap.proj g ∘ₗ δ = DistribSMul.toLinearMap A S g - LinearMap.id :=
      fun g ↦ rfl

    have hker : LinearMap.ker δ ≤ LinearMap.range (Algebra.linearMap A S) := by
      intro s hs
      have hs' : ∀ g : G, g • s = s := fun g ↦ by
        have := congrFun (LinearMap.mem_ker.mp hs) g
        rwa [hδ_apply, Pi.zero_apply, sub_eq_zero] at this
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) s hs'
      exact ⟨a, ha⟩
    have hrange : LinearMap.range (Algebra.linearMap A S) ≤ LinearMap.ker δ := by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      funext g
      rw [hδ_apply, Pi.zero_apply, sub_eq_zero, Algebra.linearMap_apply]
      exact smul_algebraMap g a

    set W : Submodule A S := LinearMap.range (Algebra.linearMap A S) with hW
    let π : S →ₗ[A] S ⧸ W := W.mkQ
    let δ' : S ⧸ W →ₗ[A] (G → S) := W.liftQ δ hrange
    have hδ' : Function.Injective δ' :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot W δ hrange hker)
    have hδ'π : δ' ∘ₗ π = δ := Submodule.liftQ_mkQ W δ hrange
    have hπ : Function.Surjective π := Submodule.mkQ_surjective W
    have hexact : Function.Exact (Algebra.linearMap A S) π := LinearMap.exact_map_mkQ_range _

    have hE : Function.Exact (map I (Algebra.linearMap A S)) (map I π) :=
      map_exact' I hι hexact hπ
    have hinjδ' : Function.Injective (map I δ') := map_injective' I hδ'
    refine ⟨map_injective' I hι, fun x ↦ ?_⟩
    constructor
    ·
      rintro ⟨a, rfl⟩ g
      rw [map_comp_apply, hfix]
    ·
      intro hx

      have hδx : map I δ x = 0 := by
        apply (piEquivOfFintype I (fun _ : G ↦ S)).injective
        rw [_root_.map_zero]
        funext g
        simp only [piEquivOfFintype_apply, AdicCompletion.pi, LinearMap.pi_apply, Pi.zero_apply]
        rw [map_comp_apply, hproj, map_sub_apply, AdicCompletion.map_id, LinearMap.id_apply, hx g,
          sub_self]
      apply (hE x).mp
      apply hinjδ'
      rw [map_comp_apply, hδ'π, hδx, _root_.map_zero]


-- created on 2026-10-09
