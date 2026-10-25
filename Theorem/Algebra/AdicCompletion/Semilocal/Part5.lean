import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.Semilocal.Part4
universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

theorem evalₐ_ofCompatibleFamily (z : ∀ n, S ⧸ I ^ n)
    (hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m) (n : ℕ) :
    evalₐ I n (ofCompatibleFamily I z hz) = z n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z n)
  rw [← hr]
  show Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n)
      (eval I S n (ofCompatibleFamily I z hz)) = Ideal.Quotient.mk (I ^ n) r
  rw [show eval I S n (ofCompatibleFamily I z hz) =
      Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n) from rfl,
    ← hr, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]

variable [IsNoetherianRing S] [IsArtinianRing (S ⧸ I)]

omit [IsArtinianRing (S ⧸ I)] in

theorem exists_uniform_exponent :
    ∃ c₁ : ℕ, (∀ n : ℕ, I.radical ^ (c₁ * n) ≤ I ^ n) ∧ (∀ n : ℕ, n ≤ c₁ * n) := by
  obtain ⟨c₀, hc₀⟩ := Ideal.exists_radical_pow_le_of_fg I (IsNoetherian.noetherian _)
  refine ⟨c₀ + 1, fun n => ?_, fun n => Nat.le_mul_of_pos_left n c₀.succ_pos⟩
  rw [pow_mul]
  refine Ideal.pow_right_mono ?_ n
  rw [pow_succ]
  exact le_trans Ideal.mul_le_left hc₀

theorem semilocalPiHom_injective : Function.Injective (semilocalPiHom I) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  refine ext_evalₐ fun n => ?_
  have hz : evalₐ I n (0 : AdicCompletion I S) = 0 := by simp
  rw [hz]
  obtain ⟨c₁, hrad, hle⟩ := exists_uniform_exponent I
  refine (Ideal.quotientPowEquivPiSup I (hrad n)).injective ?_
  change Ideal.quotientPowEquivPiSup I (hrad n) (evalₐ I n x) = 0
  funext P
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I (c₁ * n) x)
  have hev : evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := by
    rw [← factorPow_evalₐ I (hle n) x, ← hr, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
  have hP0 : evalₐ (P : Ideal S) (c₁ * n) (semilocalPiHom I x P) = 0 := by
    simp [congrFun hx P]
  rw [semilocalPiHom_apply, semilocalComponent, evalₐ_mapₐ, ← hr, levelMapₐ_mk] at hP0
  have hrP : r ∈ (P : Ideal S) ^ (c₁ * n) := by
    rwa [AlgHom.coe_id, id_eq, Ideal.Quotient.eq_zero_iff_mem] at hP0
  rw [hev, Ideal.quotientPowEquivPiSup_mk, Pi.zero_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right hrP)

omit [IsNoetherianRing S] in

theorem quotientPowEquivPiSup_factorPow {c n c' n' : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) (hc' : I.radical ^ c' ≤ I ^ n')
    (hn : n ≤ n') (hcc : c ≤ c') (z : S ⧸ I ^ n') :
    Ideal.quotientPowEquivPiSup I hc (Ideal.Quotient.factorPow I hn z) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.factor
          (sup_le_sup (Ideal.pow_le_pow_right hn) (Ideal.pow_le_pow_right hcc))
          (Ideal.quotientPowEquivPiSup I hc' z P) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective z
  funext P
  rw [← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.quotientPowEquivPiSup_mk, Ideal.quotientPowEquivPiSup_mk,
    Ideal.Quotient.factor_mk]

theorem semilocalPiHom_surjective : Function.Surjective (semilocalPiHom I) := by
  intro y
  obtain ⟨c₁, hrad, hle⟩ := exists_uniform_exponent I
  have hmono : ∀ {m n : ℕ}, m ≤ n → c₁ * m ≤ c₁ * n := fun h => Nat.mul_le_mul_left _ h

  set z : ∀ n, S ⧸ I ^ n := fun n =>
    (Ideal.quotientPowEquivPiSup I (hrad n)).symm
      (fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * n) (y P)))
    with hz_def
  have hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m := by
    intro m n hmn
    refine (Ideal.quotientPowEquivPiSup I (hrad m)).injective ?_
    rw [RingEquiv.apply_symm_apply,
      quotientPowEquivPiSup_factorPow I (hrad m) (hrad n) hmn (hmono hmn),
      RingEquiv.apply_symm_apply]
    funext P
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (P : Ideal S) (c₁ * n) (y P))
    have hsm : evalₐ (P : Ideal S) (c₁ * m) (y P) =
        Ideal.Quotient.mk ((P : Ideal S) ^ (c₁ * m)) s := by
      rw [← factorPow_evalₐ (P : Ideal S) (hmono hmn) (y P), ← hs,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [← hs, hsm, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factor_mk]
  refine ⟨ofCompatibleFamily I z hz, ?_⟩
  funext P
  refine ext_evalₐ fun k => ?_

  rw [semilocalPiHom_apply, semilocalComponent, evalₐ_mapₐ, evalₐ_ofCompatibleFamily]

  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z k)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (P : Ideal S) (c₁ * k) (y P))
  have hcomp : Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) r =
      Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) s := by
    have hzk : Ideal.quotientPowEquivPiSup I (hrad k) (z k) P =
        Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * k) (y P)) :=
      congrFun ((Ideal.quotientPowEquivPiSup I (hrad k)).apply_symm_apply
        (fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
          Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * k) (y P)))) P
    have hzk' : Ideal.quotientPowEquivPiSup I (hrad k) (z k) P =
        Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) r := by
      rw [← hr, Ideal.quotientPowEquivPiSup_mk]
    rw [← hzk', hzk, ← hs, Ideal.Quotient.factor_mk]
  have hrs : r - s ∈ (P : Ideal S) ^ k := by
    have hmem : r - s ∈ I ^ k ⊔ (P : Ideal S) ^ (c₁ * k) :=
      (Ideal.Quotient.eq).mp hcomp
    exact Ideal.sup_pow_le_pow_of_le I P.2.2 (hle k) hmem
  rw [← hr, levelMapₐ_mk, AlgHom.coe_id, id_eq,
    ← factorPow_evalₐ (P : Ideal S) (hle k) (y P), ← hs,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  exact (Ideal.Quotient.eq).mpr hrs

end AdicCompletion
end Assembly
