import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.IdeleNorm
open NumberField.TopologicalIdeleGroup


namespace NumberField.TopologicalIdeleGroup

/--
[adelicNorm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
lemma adelicNorm_apply
  [Field K] [NumberField K]
  {a : TopologicalIdeleGroup (𝓞 K) K} :
-- imply
  adelicNorm K a =
    (∏ w : InfinitePlace K, ‖(a.1 w : w.Completion)‖ ^ w.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ‖(a.2 v : v.adicCompletion K)‖ :=
-- proof
  rfl

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[mem_normOneIdeles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
lemma mem_normOneIdeles
  [Field K] [NumberField K]
  {a : TopologicalIdeleGroup (𝓞 K) K} :
-- imply
  a ∈ normOneIdeles K ↔ adelicNorm K a = 1 :=
-- proof
  MonoidHom.mem_ker

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[adelicNorm_principalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
lemma adelicNorm_principalEmbedding
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  adelicNorm K (principalEmbedding (𝓞 K) K x) = 1 := by
-- proof
  rw [adelicNorm_apply, principalEmbedding_fst, principalEmbedding_snd]
  have hinf : (∏ w : NumberField.InfinitePlace K,
    ‖((infinitePrincipalEmbedding K x w : w.Completion))‖ ^ w.mult) =
    ∏ w : NumberField.InfinitePlace K, w ((x : K)) ^ w.mult := by
    apply Finset.prod_congr rfl
    intro w _
    rw [infinitePrincipalEmbedding_apply (R := 𝓞 K), Units.coe_map]
    change ‖algebraMap K w.Completion (x : K)‖ ^ w.mult = w (x : K) ^ w.mult
    have hco : algebraMap K w.Completion ((x : K)) =
      ((WithAbs.equiv w.1).symm ((x : K)) : w.Completion) := rfl
    rw [hco, NumberField.InfinitePlace.Completion.norm_coe]
    simp
  have hpt : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ‖((finitePrincipalEmbedding (𝓞 K) K x v :
      v.adicCompletion K))‖ =
      (NumberField.FinitePlace.equivHeightOneSpectrum.symm v) ((x : K)) := by
    intro v
    rw [finitePrincipalEmbedding_apply (R := 𝓞 K), Units.coe_map]
    exact (NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply
      v ((x : K))).symm
  have hfun : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    ‖((finitePrincipalEmbedding (𝓞 K) K x v :
      v.adicCompletion K))‖) =
    (fun v => (NumberField.FinitePlace.equivHeightOneSpectrum.symm v)
      ((x : K))) := funext hpt
  have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ‖((finitePrincipalEmbedding (𝓞 K) K x v :
      v.adicCompletion K))‖) =
    ∏ᶠ w : NumberField.FinitePlace K, w ((x : K)) := by
    rw [hfun]
    exact @finprod_comp_equiv (IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (NumberField.FinitePlace K) ℝ _
      NumberField.FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w => w ((x : K)))
  rw [hinf, hfin]
  exact NumberField.prod_abs_eq_one (Units.ne_zero x)

end NumberField.TopologicalIdeleGroup

namespace NumberField.TopologicalIdeleGroup

/--
[principalIdeles_le_normOneIdeles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/IdeleNorm.lean)
-/
@[path]
lemma principalIdeles_le_normOneIdeles
  [Field K] [NumberField K] :
-- imply
  principalIdeles (𝓞 K) K ≤ normOneIdeles K := by
-- proof
  intro a ha
  obtain ⟨x, rfl⟩ := ha
  rw [mem_normOneIdeles, adelicNorm_principalEmbedding]

end NumberField.TopologicalIdeleGroup


-- created on 2026-10-20
-- updated on 2026-10-29
