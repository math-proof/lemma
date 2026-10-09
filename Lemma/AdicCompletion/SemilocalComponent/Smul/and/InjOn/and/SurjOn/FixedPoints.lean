import sympy.Basic
import Mathlib
import Lemma.AdicCompletion.Mem.NonZeroDivisors.AlgebraMap.of.Mem.NonZeroDivisors.of.LiesOver
import Lemma.AdicCompletion.exists.RingEquiv.of.IsLocalization.AtPrime.of.IsMaximal

/-!
Port of FLT `Def_AdicCompletionGaloisAction` (MulSemiringAction on AdicCompletion),
reusing `AdicCompletion.mapₐ` / `mapₐ_of` / `evalₐ_mapₐ` / `levelMapₐ_mk` /
`factorPow_evalₐ` from the IsLocalization port of RingFunctoriality.
-/

open scoped Pointwise

namespace AdicCompletion
namespace GaloisAction
end GaloisAction

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section Generic

variable (I : Ideal C)

theorem map_toIntAlgHom_le_of_smul_eq (g : G) (h : g • I = I) :
    I.map (MulSemiringAction.toRingHom G C g).toIntAlgHom ≤ I := by
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap]
  have hmem : g • c ∈ g • I := Ideal.smul_mem_pointwise_smul g c I hc
  rw [h] at hmem
  exact hmem

noncomputable def smulAlgHom (h : ∀ g : G, g • I = I) (g : G) :
    AdicCompletion I C →ₐ[ℤ] AdicCompletion I C :=
  mapₐ I I (MulSemiringAction.toRingHom G C g).toIntAlgHom (map_toIntAlgHom_le_of_smul_eq I g (h g))

theorem smulAlgHom_of (h : ∀ g : G, g • I = I) (g : G) (c : C) :
    smulAlgHom I h g (of I C c) = of I C (g • c) := by
  rw [smulAlgHom, mapₐ_of]
  rfl

theorem evalₐ_smulAlgHom (h : ∀ g : G, g • I = I) (g : G) (n : ℕ) (c : C)
    (x : AdicCompletion I C) (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    evalₐ I n (smulAlgHom I h g x) = Ideal.Quotient.mk (I ^ n) (g • c) := by
  rw [smulAlgHom, evalₐ_mapₐ, hx, levelMapₐ_mk]
  rfl

@[reducible]
noncomputable def mulSemiringActionOfSMulEq (h : ∀ g : G, g • I = I) :
    MulSemiringAction G (AdicCompletion I C) where
  smul g x := smulAlgHom I h g x
  one_smul x := by
    apply ext_evalₐ
    intro n
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    show evalₐ I n (smulAlgHom I h 1 x) = _
    rw [evalₐ_smulAlgHom I h 1 n c x hc.symm, one_smul, hc]
  mul_smul g g' x := by
    apply ext_evalₐ
    intro n
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    show evalₐ I n (smulAlgHom I h (g * g') x)
      = evalₐ I n (smulAlgHom I h g (smulAlgHom I h g' x))
    rw [evalₐ_smulAlgHom I h (g * g') n c x hc.symm,
      evalₐ_smulAlgHom I h g n (g' • c) _ (evalₐ_smulAlgHom I h g' n c x hc.symm), mul_smul]
  smul_zero g := _root_.map_zero (smulAlgHom I h g)
  smul_add g x y := _root_.map_add (smulAlgHom I h g) x y
  smul_one g := _root_.map_one (smulAlgHom I h g)
  smul_mul g x y := _root_.map_mul (smulAlgHom I h g) x y

end Generic

section Stabilizer

variable (𝔫 : Ideal C)

@[reducible]
noncomputable def instMulSemiringActionStabilizer :
    MulSemiringAction (MulAction.stabilizer G 𝔫) (AdicCompletion 𝔫 C) :=
  mulSemiringActionOfSMulEq 𝔫 (fun d => d.2)

attribute [instance] instMulSemiringActionStabilizer

end Stabilizer

section MapIdeal

variable {O : Type w} [CommRing O] [Algebra O C]

theorem smul_algebraMap_eq [SMulCommClass G O C] (g : G) (o : O) :
    g • algebraMap O C o = algebraMap O C o := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

theorem smul_map_algebraMap_eq [SMulCommClass G O C] (J : Ideal O) (g : G) :
    g • J.map (algebraMap O C) = J.map (algebraMap O C) := by
  rw [Ideal.pointwise_smul_def, Ideal.map_map]
  congr 1
  ext o
  exact smul_algebraMap_eq g o

@[reducible]
noncomputable def instMulSemiringActionMap [SMulCommClass G O C] (J : Ideal O) :
    MulSemiringAction G (AdicCompletion (J.map (algebraMap O C)) C) :=
  mulSemiringActionOfSMulEq _ (smul_map_algebraMap_eq J)

attribute [instance] instMulSemiringActionMap

end MapIdeal


section EvalSmul
variable (I : Ideal C)
theorem evalₐ_smul' (h : ∀ g : G, g • I = I) (g : G) (n : ℕ) (c : C) (x : AdicCompletion I C)
    (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    (letI := mulSemiringActionOfSMulEq I h; evalₐ I n (g • x)) = Ideal.Quotient.mk (I ^ n) (g • c) :=
  evalₐ_smulAlgHom I h g n c x hx

theorem evalₐ_stabilizer_smul (𝔫 : Ideal C) (d : MulAction.stabilizer G 𝔫) (n : ℕ) (c : C)
    (x : AdicCompletion 𝔫 C) (hx : evalₐ 𝔫 n x = Ideal.Quotient.mk (𝔫 ^ n) c) :
    evalₐ 𝔫 n (d • x) = Ideal.Quotient.mk (𝔫 ^ n) ((d : G) • c) :=
  evalₐ_smul' 𝔫 (fun d => d.2) d n c x hx

variable {O : Type w} [CommRing O] [Algebra O C]
theorem evalₐ_map_smul [SMulCommClass G O C] (J : Ideal O) (g : G) (n : ℕ) (c : C)
    (x : AdicCompletion (J.map (algebraMap O C)) C)
    (hx : evalₐ (J.map (algebraMap O C)) n x = Ideal.Quotient.mk _ c) :
    evalₐ (J.map (algebraMap O C)) n (g • x) = Ideal.Quotient.mk _ (g • c) :=
  evalₐ_smul' _ (smul_map_algebraMap_eq J) g n c x hx
end EvalSmul

end AdicCompletion


namespace AdicCompletion
section IndInvHelpers

open scoped Pointwise
open scoped AdicCompletion.GaloisAction

universe u₁ u₂ u₃

variable {O : Type u₁} [CommRing O] {S : Type u₂} [CommRing S] [Algebra O S]
variable {G : Type u₃} [Group G] [MulSemiringAction G S]

theorem indinv_evalₐ_semilocalComponent (I : Ideal S) {Q : Ideal S} (hIQ : I ≤ Q) (n : ℕ)
    (c : S) (x : AdicCompletion I S) (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    evalₐ Q n (semilocalComponent I hIQ x) = Ideal.Quotient.mk (Q ^ n) c := by
  rw [semilocalComponent, evalₐ_mapₐ, hx, levelMapₐ_mk]
  rfl

theorem indinv_evalₐ_mapₐ_smul (g : G) {Q Q' : Ideal S}
    (h : Q.map (MulSemiringAction.toRingHom G S g).toIntAlgHom ≤ Q') (n : ℕ) (c : S)
    (y : AdicCompletion Q S) (hy : evalₐ Q n y = Ideal.Quotient.mk (Q ^ n) c) :
    evalₐ Q' n (mapₐ Q Q' (MulSemiringAction.toRingHom G S g).toIntAlgHom h y) =
      Ideal.Quotient.mk (Q' ^ n) (g • c) := by
  rw [evalₐ_mapₐ, hy, levelMapₐ_mk]
  rfl

theorem indinv_map_le_of_eq_smul (a : G) {P Q : Ideal S} (hQ : Q = a • P) :
    P.map (MulSemiringAction.toRingHom G S a).toIntAlgHom ≤ Q := by
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  rw [Ideal.mem_comap, hQ]
  exact Ideal.smul_mem_pointwise_smul a s P hs

theorem indinv_smul_sub_smul_mem_pow (g : G) {P : Ideal S} {n : ℕ} {a b : S}
    (h : a - b ∈ P ^ n) : g • a - g • b ∈ (g • P) ^ n := by
  rw [← smul_sub, ← smul_pow']
  exact Ideal.smul_mem_pointwise_smul g _ _ h

theorem indinv_sub_mem_trans {K : Ideal S} {a b c : S} (h₁ : a - b ∈ K) (h₂ : b - c ∈ K) :
    a - c ∈ K := by
  have h := K.add_mem h₁ h₂
  rwa [sub_add_sub_cancel] at h

theorem indinv_sub_mem_symm {K : Ideal S} {a b : S} (h : a - b ∈ K) : b - a ∈ K := by
  have h' := K.neg_mem h
  rwa [neg_sub] at h'

variable [SMulCommClass G O S] (J : Ideal O)

theorem indinv_smul_semilocalComponent_of_forall_smul_eq (P : Ideal S)
    (hJP : J.map (algebraMap O S) ≤ P)
    (x : AdicCompletion (J.map (algebraMap O S)) S) (hx : ∀ g : G, g • x = x)
    (d : MulAction.stabilizer G P) :
    d • semilocalComponent (J.map (algebraMap O S)) hJP x =
      semilocalComponent (J.map (algebraMap O S)) hJP x := by
  refine ext_evalₐ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ (J.map (algebraMap O S)) n x)
  have h1 : evalₐ P n (semilocalComponent (J.map (algebraMap O S)) hJP x) =
      Ideal.Quotient.mk (P ^ n) c :=
    indinv_evalₐ_semilocalComponent _ hJP n c x hc.symm
  have h2 : evalₐ (J.map (algebraMap O S)) n ((d : G) • x) =
      Ideal.Quotient.mk _ ((d : G) • c) :=
    evalₐ_map_smul J (d : G) n c x hc.symm
  rw [hx] at h2
  rw [evalₐ_stabilizer_smul P d n c _ h1]
  exact (indinv_evalₐ_semilocalComponent _ hJP n _ x h2).symm

variable [IsNoetherianRing S] [IsArtinianRing (S ⧸ J.map (algebraMap O S))]

theorem indinv_eq_of_semilocalComponent_eq (P : Ideal S) (hJP : J.map (algebraMap O S) ≤ P)
    (htrans : ∀ Q : Ideal S, Q.IsMaximal → J.map (algebraMap O S) ≤ Q → ∃ g : G, Q = g • P)
    (x y : AdicCompletion (J.map (algebraMap O S)) S) (hx : ∀ g : G, g • x = x)
    (hy : ∀ g : G, g • y = y)
    (hxy : semilocalComponent (J.map (algebraMap O S)) hJP x =
      semilocalComponent (J.map (algebraMap O S)) hJP y) :
    x = y := by
  refine semilocalPiHom_injective (J.map (algebraMap O S)) (funext fun Q => ?_)
  have hQ := htrans Q.1 Q.2.1 Q.2.2
  obtain ⟨g, hg⟩ := hQ
  rw [semilocalPiHom_apply, semilocalPiHom_apply]
  refine ext_evalₐ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ (J.map (algebraMap O S)) n x)
  obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (evalₐ (J.map (algebraMap O S)) n y)
  have hP : c - c' ∈ P ^ n := by
    refine Ideal.Quotient.eq.mp ?_
    rw [← indinv_evalₐ_semilocalComponent _ hJP n c x hc.symm,
      ← indinv_evalₐ_semilocalComponent _ hJP n c' y hc'.symm, hxy]
  have hxg : evalₐ (J.map (algebraMap O S)) n x = Ideal.Quotient.mk _ (g • c) := by
    rw [← evalₐ_map_smul J g n c x hc.symm, hx]
  have hyg : evalₐ (J.map (algebraMap O S)) n y = Ideal.Quotient.mk _ (g • c') := by
    rw [← evalₐ_map_smul J g n c' y hc'.symm, hy]
  rw [indinv_evalₐ_semilocalComponent _ Q.2.2 n _ x hxg,
    indinv_evalₐ_semilocalComponent _ Q.2.2 n _ y hyg]
  refine Ideal.Quotient.eq.mpr ?_
  have h := indinv_smul_sub_smul_mem_pow g hP
  rw [← hg] at h
  exact h

theorem indinv_exists_of_forall_stabilizer_smul_eq (P : Ideal S) [P.IsMaximal]
    (hJP : J.map (algebraMap O S) ≤ P)
    (htrans : ∀ Q : Ideal S, Q.IsMaximal → J.map (algebraMap O S) ≤ Q → ∃ g : G, Q = g • P)
    (z : AdicCompletion P S) (hz : ∀ d : MulAction.stabilizer G P, d • z = z) :
    ∃ x : AdicCompletion (J.map (algebraMap O S)) S, (∀ g : G, g • x = x) ∧
      semilocalComponent (J.map (algebraMap O S)) hJP x = z := by
  have hmem : ∀ a : G, (a • P).IsMaximal ∧ J.map (algebraMap O S) ≤ a • P := fun a => by
    have hle : J.map (algebraMap O S) ≤ a • P :=
      calc J.map (algebraMap O S) = a • J.map (algebraMap O S) := (smul_map_algebraMap_eq J a).symm
        _ ≤ a • P := smul_mono_right a hJP
    exact ⟨Ideal.isMaximal_of_isPrime_of_le _ (a • P) hle, hle⟩
  have htrans' : ∀ Q : {P : Ideal S // P.IsMaximal ∧ J.map (algebraMap O S) ≤ P},
      ∃ g : G, (Q : Ideal S) = g • P := fun Q => htrans Q.1 Q.2.1 Q.2.2
  choose γ hγ using htrans'
  have hsurj := semilocalPiHom_surjective (J.map (algebraMap O S))
    (fun Q => mapₐ P (Q : Ideal S) (MulSemiringAction.toRingHom G S (γ Q)).toIntAlgHom
      (indinv_map_le_of_eq_smul (γ Q) (hγ Q)) z)
  obtain ⟨x, hx⟩ := hsurj
  have hxw : ∀ Q : {P : Ideal S // P.IsMaximal ∧ J.map (algebraMap O S) ≤ P},
      semilocalComponent (J.map (algebraMap O S)) Q.2.2 x =
        mapₐ P (Q : Ideal S) (MulSemiringAction.toRingHom G S (γ Q)).toIntAlgHom
          (indinv_map_le_of_eq_smul (γ Q) (hγ Q)) z := fun Q => by
    rw [← semilocalPiHom_apply, hx]
  have wd : ∀ (n : ℕ) (e : S), Ideal.Quotient.mk (P ^ n) e = evalₐ P n z →
      ∀ a b : G, a • P = b • P → a • e - b • e ∈ (a • P) ^ n := by
    intro n e he a b hab
    have hd : a⁻¹ * b ∈ MulAction.stabilizer G P := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hab, inv_smul_smul]
    have h1 : evalₐ P n ((⟨a⁻¹ * b, hd⟩ : MulAction.stabilizer G P) • z) =
        Ideal.Quotient.mk (P ^ n) ((a⁻¹ * b) • e) :=
      evalₐ_stabilizer_smul P ⟨a⁻¹ * b, hd⟩ n e z he.symm
    rw [hz] at h1
    have h2 : e - (a⁻¹ * b) • e ∈ P ^ n := Ideal.Quotient.eq.mp (he.trans h1)
    have h3 := indinv_smul_sub_smul_mem_pow a h2
    rwa [smul_smul, mul_inv_cancel_left] at h3
  refine ⟨x, fun g => ?_, ?_⟩
  · refine semilocalPiHom_injective (J.map (algebraMap O S)) (funext fun Q => ?_)
    rw [semilocalPiHom_apply, semilocalPiHom_apply]
    refine ext_evalₐ fun n => ?_
    obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (evalₐ P n z)
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ (J.map (algebraMap O S)) n x)
    have star : ∀ Q' : {P : Ideal S // P.IsMaximal ∧ J.map (algebraMap O S) ≤ P},
        c - γ Q' • e ∈ (Q' : Ideal S) ^ n := fun Q' => by
      refine Ideal.Quotient.eq.mp ?_
      rw [← indinv_evalₐ_semilocalComponent _ Q'.2.2 n c x hc.symm, hxw Q',
        indinv_evalₐ_mapₐ_smul (γ Q') _ n e z he.symm]
    have hxg : evalₐ (J.map (algebraMap O S)) n (g • x) = Ideal.Quotient.mk _ (g • c) :=
      evalₐ_map_smul J g n c x hc.symm
    rw [indinv_evalₐ_semilocalComponent _ Q.2.2 n _ (g • x) hxg,
      indinv_evalₐ_semilocalComponent _ Q.2.2 n c x hc.symm]
    refine Ideal.Quotient.eq.mpr ?_
    have hQ₀ := hmem (g⁻¹ * γ Q)
    have hab : (g * γ ⟨(g⁻¹ * γ Q) • P, hQ₀⟩) • P = γ Q • P := by
      rw [mul_smul, ← hγ ⟨(g⁻¹ * γ Q) • P, hQ₀⟩]
      show g • (g⁻¹ * γ Q) • P = γ Q • P
      rw [smul_smul, mul_inv_cancel_left]
    have h1 : g • c - (g * γ ⟨(g⁻¹ * γ Q) • P, hQ₀⟩) • e ∈ (Q : Ideal S) ^ n := by
      have h := indinv_smul_sub_smul_mem_pow g (star ⟨(g⁻¹ * γ Q) • P, hQ₀⟩)
      rw [smul_smul g (γ ⟨(g⁻¹ * γ Q) • P, hQ₀⟩) e] at h
      have hQ : g • (g⁻¹ * γ Q) • P = (Q : Ideal S) := by
        rw [smul_smul, mul_inv_cancel_left]
        exact (hγ Q).symm
      rw [← hQ]
      exact h
    have h2 : (g * γ ⟨(g⁻¹ * γ Q) • P, hQ₀⟩) • e - γ Q • e ∈ (Q : Ideal S) ^ n := by
      have h := wd n e he _ _ hab
      rw [hab, ← hγ Q] at h
      exact h
    exact indinv_sub_mem_trans (indinv_sub_mem_trans h1 h2) (indinv_sub_mem_symm (star Q))
  · have hPw := hxw ⟨P, ‹P.IsMaximal›, hJP⟩
    refine ext_evalₐ fun n => ?_
    obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (evalₐ P n z)
    have hev : evalₐ P n (semilocalComponent (J.map (algebraMap O S)) hJP x) =
        Ideal.Quotient.mk (P ^ n) (γ ⟨P, ‹P.IsMaximal›, hJP⟩ • e) := by
      rw [hPw]
      exact indinv_evalₐ_mapₐ_smul _ _ n e z he.symm
    rw [hev, ← he]
    refine Ideal.Quotient.eq.mpr (indinv_sub_mem_symm ?_)
    have h := wd n e he 1 (γ ⟨P, ‹P.IsMaximal›, hJP⟩)
      (by rw [one_smul]; exact hγ ⟨P, ‹P.IsMaximal›, hJP⟩)
    rwa [one_smul, one_smul] at h

end IndInvHelpers
end AdicCompletion


/--
[AdicCompletion_semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_semilocalComponent_smul_and_injOn_and_surjOn_fixedPoints.lean)
-/
@[path]
private lemma main
  {O : Type*} [CommRing O] {S : Type*} [CommRing S] [IsNoetherianRing S] [Algebra O S] {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G O S]
-- given
  (J : Ideal O) [IsArtinianRing (S ⧸ J.map (algebraMap O S))] (P : Ideal S) [P.IsMaximal] (hJP : J.map (algebraMap O S) ≤ P) (htrans : ∀ Q : Ideal S, Q.IsMaximal → J.map (algebraMap O S) ≤ Q → ∃ g : G, Q = g • P) :
-- imply
  (∀ x : AdicCompletion (J.map (algebraMap O S)) S, (∀ g : G, g • x = x) →
      ∀ d : MulAction.stabilizer G P,
        d • AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x =
          AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x) ∧
    (∀ x y : AdicCompletion (J.map (algebraMap O S)) S, (∀ g : G, g • x = x) → (∀ g : G, g • y = y) →
      AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x =
        AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP y → x = y) ∧
    (∀ z : AdicCompletion P S, (∀ d : MulAction.stabilizer G P, d • z = z) →
      ∃ x : AdicCompletion (J.map (algebraMap O S)) S, (∀ g : G, g • x = x) ∧
        AdicCompletion.semilocalComponent (J.map (algebraMap O S)) hJP x = z) :=
-- proof
  ⟨fun x hx d =>
      AdicCompletion.indinv_smul_semilocalComponent_of_forall_smul_eq J P hJP x hx d,
    fun x y hx hy hxy =>
      AdicCompletion.indinv_eq_of_semilocalComponent_eq J P hJP htrans x y hx hy hxy,
    fun z hz =>
      AdicCompletion.indinv_exists_of_forall_stabilizer_smul_eq J P hJP htrans z hz⟩


-- created on 2026-10-09
