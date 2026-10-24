import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Cor2344
open TateCohomology
open Finset CategoryTheory


namespace TateCohomology

/--
[herbrandQuotient_eq_one_of_finite'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2344.lean)
-/
@[path]
lemma herbrandQuotient_eq_one_of_finite'
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [IsCyclic G]
  {A : Rep k G}
  [Finite A]
  [Fintype (tateH0 A)]
  [Fintype (tateMinus1 A)] :
-- imply
  herbrandQuotient A = 1 := by
-- proof
  have heq := herbrand_quotient_eq_one_of_finite A
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at heq
  unfold herbrandQuotient
  rw [heq]
  have hpos : (0 : ℚ) < Fintype.card (tateMinus1 A) := by
    exact_mod_cast Fintype.card_pos (α := tateMinus1 A)
  exact div_self hpos.ne'

end TateCohomology

namespace TateCohomology

/--
[finite_of_shortExact_torsion_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2344.lean)
-/
@[path]
lemma finite_of_shortExact_torsion_fg
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  {S : ShortComplex (Rep ℤ G₀)}
-- given
  (hS : S.ShortExact)
  (htors : Module.IsTorsion ℤ S.X₁)
  (hfg : Module.Finite ℤ S.X₂) :
-- imply
  Finite (S.X₁ : Rep ℤ G₀) := by
-- proof
  let φ : ↑S.X₁ →+ ↑S.X₂ :=
    { toFun := S.f.hom
      map_zero' := by simp [map_zero]
      map_add' := by simp [map_add] }
  let ψ : ↑S.X₁ →ₗ[ℤ] ↑S.X₂ := φ.toIntLinearMap
  have hinj : Function.Injective ψ := by
    intro a b hab
    have := hS.mono_f
    exact (Rep.mono_iff_injective S.f).mp this hab
  haveI : IsNoetherian ℤ S.X₂ := isNoetherian_of_isNoetherianRing_of_finite ℤ (↑S.X₂)
  haveI : Module.Finite ℤ S.X₁ := Module.Finite.of_injective ψ hinj
  exact Module.finite_of_fg_torsion _ htors

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_eq_shortExact_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2344.lean)
-/
@[path]
lemma herbrandQuotient_eq_shortExact_torsion
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  [IsCyclic G₀]
  {S : ShortComplex (Rep ℤ G₀)}
  [Fintype (tateH0 S.X₂)]
  [Fintype (tateMinus1 S.X₂)]
  [Fintype (tateH0 S.X₃)]
  [Fintype (tateMinus1 S.X₃)]
-- given
  (hS : S.ShortExact)
  (htors : Module.IsTorsion ℤ S.X₁)
  (hfg : Module.Finite ℤ S.X₂) :
-- imply
  herbrandQuotient S.X₂ = herbrandQuotient S.X₃ := by
-- proof
  haveI : Finite (S.X₁ : Rep ℤ G₀) := finite_of_shortExact_torsion_fg hS htors hfg
  haveI : Fintype (tateH0 S.X₁) := Fintype.ofFinite _
  haveI : Fintype (tateMinus1 S.X₁) := Fintype.ofFinite _
  have hmult := herbrandQuotient_multiplicative hS
  have hone := herbrandQuotient_eq_one_of_finite' S.X₁
  rw [hmult, hone, one_mul]

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_trivial_pow_clean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2344.lean)
-/
@[path]
lemma herbrandQuotient_trivial_pow_clean
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  [IsCyclic G₀]
  {M : Type}
  [AddCommGroup M]
  [Module.Finite ℤ M]
  [Fintype (tateH0 (Rep.trivial ℤ G₀ M))]
  [Fintype (tateMinus1 (Rep.trivial ℤ G₀ M))] :
-- imply
  herbrandQuotient (Rep.trivial ℤ G₀ M) = (Fintype.card G₀ : ℚ) ^ (Module.finrank ℤ M) := by
-- proof
  set Q := M ⧸ Submodule.torsion ℤ M with hQ_def
  haveI : Module.IsTorsionFree ℤ Q := Submodule.QuotientTorsion.instIsTorsionFree
  haveI : Module.Finite ℤ Q := Module.Finite.quotient ℤ (Submodule.torsion ℤ M)
  haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  let n := Module.finrank ℤ Q
  let eQ : Q ≃ₗ[ℤ] (Fin n → ℤ) := (Module.finBasis ℤ Q).equivFun
  have hrank : Module.finrank ℤ M = n := by
    simp only [Module.finrank, n]
    congr 1
    exact (rank_quotient_eq_of_le_torsion (le_refl (Submodule.torsion ℤ M))).symm
  let β : M →ₗ[ℤ] (Fin n → ℤ) := eQ.toLinearMap.comp (Submodule.torsion ℤ M).mkQ
  let α : Rep.trivial ℤ G₀ M ⟶ Rep.trivial ℤ G₀ (Fin n → ℤ) := Rep.trivialHom β
  haveI : IsNoetherian ℤ M := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  haveI : Module.Finite ℤ (Submodule.torsion ℤ M) :=
    Module.IsNoetherian.finite ℤ (↥(Submodule.torsion ℤ M))
  haveI hfin_tor : Finite (↑(Submodule.torsion ℤ M)) :=
    Module.finite_of_fg_torsion _ Submodule.torsion_isTorsion
  have hβ_surj : Function.Surjective β := by
    intro p
    obtain ⟨q, hq⟩ := eQ.surjective p
    obtain ⟨m, hm⟩ := Submodule.mkQ_surjective _ q
    exact ⟨m, by subst hm; subst hq; rfl⟩
  haveI hfin_ker : Finite (Limits.kernel α : Rep ℤ G₀) := by
    have h_inj : Function.Injective (Limits.kernel.ι α).hom := by
      rw [← Rep.mono_iff_injective]; exact inferInstance
    have h_in_tor : ∀ x : (Limits.kernel α : Rep ℤ G₀),
      (Limits.kernel.ι α).hom x ∈ Submodule.torsion ℤ M := by
      intro x
      have hcond := Limits.kernel.condition (f := α)
      have hx : (α.hom) ((Limits.kernel.ι α).hom x) = 0 := by
        have := congr_arg Rep.Hom.hom hcond
        exact congr_fun (congr_arg DFunLike.coe this) x
      change β ((Limits.kernel.ι α).hom x) = 0 at hx
      have hmkq : (Submodule.torsion ℤ M).mkQ ((Limits.kernel.ι α).hom x) = 0 := by
        exact eQ.map_eq_zero_iff.mp hx
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmkq
    let ι_tor : ↑(Limits.kernel α : Rep ℤ G₀) → ↥(Submodule.torsion ℤ M) :=
      fun x => ⟨(Limits.kernel.ι α).hom x, h_in_tor x⟩
    have h_ι_tor_inj : Function.Injective ι_tor := by
      intro a b hab
      simp only [ι_tor, Subtype.mk.injEq] at hab
      exact h_inj hab
    exact Finite.of_injective ι_tor h_ι_tor_inj
  haveI hfin_coker : Finite (Limits.cokernel α : Rep ℤ G₀) := by
    haveI : Epi α := by
      rw [Rep.epi_iff_surjective]
      show Function.Surjective α.hom
      exact hβ_surj
    have hz := Limits.isZero_cokernel_of_epi α
    haveI : Subsingleton (Limits.cokernel α : Rep ℤ G₀) := by
      constructor; intro a b
      have : ∀ x : (Limits.cokernel α : Rep ℤ G₀), x = 0 := by
        intro x
        have key := congr_arg (fun g =>
          (show Limits.cokernel α ⟶ Limits.cokernel α from g).hom)
          (hz.eq_of_src (𝟙 (Limits.cokernel α)) 0)
        have := congr_fun (congr_arg DFunLike.coe key) x
        simpa using this
      rw [this a, this b]
    exact Finite.of_subsingleton
  haveI : Fintype (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ))) := Fintype.ofFinite _
  haveI : Fintype (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) := Fintype.ofFinite _
  have h_MZ : herbrandQuotient (Rep.trivial ℤ G₀ M) =
    herbrandQuotient (Rep.trivial ℤ G₀ (Fin n → ℤ)) := herbrandQuotient_eq_of_finite_kernel_cokernel α
  have h_fin : herbrandQuotient (Rep.trivial ℤ G₀ (Fin n → ℤ)) =
    (Fintype.card G₀ : ℚ) ^ n := herbrandQuotient_trivial_finFun G₀ n
  rw [h_MZ, h_fin, hrank]

end TateCohomology


-- created on 2026-10-23
