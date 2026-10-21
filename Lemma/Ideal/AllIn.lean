import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank.lean)
-/
@[path]
private lemma main
  (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
  (S : Finset (Ideal R)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsPrime)
  (hsum : ∑ 𝔭 ∈ S, Module.finrank F (R ⧸ 𝔭) = Module.finrank F R) :
  -- imply
  ∀ 𝔭 : Ideal R, 𝔭.IsPrime → 𝔭 ∈ S := by
  -- proof
  classical
  let _ : IsArtinianRing R := IsArtinianRing.of_finite F R
  intro 𝔮 h𝔮
  by_contra hq
  have hmax : ∀ 𝔭 ∈ insert 𝔮 S, 𝔭.IsMaximal := by
    intro 𝔭 hp
    obtain h | hp := Finset.mem_insert.mp hp
    ·
      rw [h]
      let _ := h𝔮
      apply IsArtinianRing.isMaximal_of_isPrime 𝔮
    ·
      let _ := hS 𝔭 hp
      apply IsArtinianRing.isMaximal_of_isPrime 𝔭
  set T : Finset (Ideal R) := insert 𝔮 S with hT
  have hcop : Pairwise fun (i j : ↥T) => IsCoprime (i : Ideal R) (j : Ideal R) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    apply Ideal.IsMaximal.coprime_of_ne (hmax i i.2) (hmax j j.2) (fun h => hij (Subtype.ext h))
  let hfin : ∀ p : ↥T, Module.Finite F (R ⧸ (p : Ideal R)) := fun p => Module.Finite.of_surjective (Ideal.Quotient.mkₐ F (p : Ideal R)).toLinearMap (Ideal.Quotient.mkₐ_surjective F _)
  let hfree : ∀ p : ↥T, Module.Free F (R ⧸ (p : Ideal R)) := fun p => Module.Free.of_divisionRing F _
  let φ : R →ₗ[F] (∀ p : ↥T, R ⧸ (p : Ideal R)) := LinearMap.pi fun p => (Ideal.Quotient.mkₐ F (p : Ideal R)).toLinearMap
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨xb, hxb⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xb
    refine ⟨x, ?_⟩
    rw [← hxb]
    ext p
    rfl
  have hle : Module.finrank F (∀ p : ↥T, R ⧸ (p : Ideal R)) ≤ Module.finrank F R := LinearMap.finrank_le_finrank_of_surjective hφ
  rw [Module.finrank_pi_fintype, Finset.sum_coe_sort T (fun p => Module.finrank F (R ⧸ p)), hT, Finset.sum_insert hq, hsum] at hle
  let _ := h𝔮
  let _ : Nontrivial (R ⧸ 𝔮) := inferInstance
  let _ : Module.Finite F (R ⧸ 𝔮) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ F 𝔮).toLinearMap (Ideal.Quotient.mkₐ_surjective F _)
  have hpos : 0 < Module.finrank F (R ⧸ 𝔮) := Module.finrank_pos
  omega


-- created on 2026-10-20
