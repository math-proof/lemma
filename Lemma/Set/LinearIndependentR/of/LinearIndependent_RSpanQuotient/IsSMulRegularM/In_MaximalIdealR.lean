import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise


/--
[QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Fintype ι]
  {x : R}
  {m : ι → M}
-- given
  (hx : x ∈ IsLocalRing.maximalIdeal R)
  (hreg : IsSMulRegular M x)
  (hli : LinearIndependent (R ⧸ Ideal.span {x}) (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M))) :
-- imply
  LinearIndependent R m := by
-- proof
  classical
    have hker_le : LinearMap.ker (Fintype.linearCombination R m) ≤
        Ideal.span {x} • LinearMap.ker (Fintype.linearCombination R m) := by
      intro a ha
      rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at ha
      have hcoeff : ∀ i, Ideal.Quotient.mk (Ideal.span {x}) (a i) = 0 := by
        have h0 : ∑ i, (Ideal.Quotient.mk (Ideal.span {x}) (a i)) •
            (Submodule.Quotient.mk (m i) : QuotSMulTop x M) = 0 := by
          have hterm : ∀ i, (Ideal.Quotient.mk (Ideal.span {x}) (a i)) •
              (Submodule.Quotient.mk (m i) : QuotSMulTop x M) =
                (Submodule.mkQ (x • ⊤ : Submodule R M)) (a i • m i) := fun i => rfl
          simp_rw [hterm, ← map_sum, ha, map_zero]
        refine Fintype.linearIndependent_iff.mp hli _ h0
      have hdvd : ∀ i, x ∣ a i := fun i =>
        Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hcoeff i))
      choose c hc using hdvd
      have ha_eq : a = x • c := funext fun i => by
        rw [Pi.smul_apply, smul_eq_mul]; exact hc i
      have hc_ker : c ∈ LinearMap.ker (Fintype.linearCombination R m) := by
        rw [LinearMap.mem_ker]
        apply hreg
        show x • Fintype.linearCombination R m c = x • (0 : M)
        rwa [smul_zero, ← map_smul, ← ha_eq]
      rw [ha_eq]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hc_ker
    have hjac : Ideal.span {x} ≤ Ideal.jacobson ⊥ :=
      le_trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
        (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    have hker : LinearMap.ker (Fintype.linearCombination R m) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _
        (IsNoetherian.noetherian _) hker_le hjac
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg_ker : g ∈ LinearMap.ker (Fintype.linearCombination R m) := by
      rwa [LinearMap.mem_ker, Fintype.linearCombination_apply]
    rw [hker, Submodule.mem_bot] at hg_ker
    exact congrFun hg_ker i


-- created on 2026-10-23
