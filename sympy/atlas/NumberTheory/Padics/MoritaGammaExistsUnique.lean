/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean -/

import sympy.atlas.NumberTheory.Padics.MoritaGamma
import Lemma.Nat.Padics.MoritaGamma
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Existence of Morita's p-adic gamma function
-/

section
namespace MetaMathlibExt

/-- The unit of `ZMod (p ^ (s+1))` attached to `k` with `¬ p ∣ k`. -/
private noncomputable def unitOfNotDvd (p s k : ℕ) [Fact p.Prime] (hk : ¬ p ∣ k) :
    (ZMod (p ^ (s + 1)))ˣ :=
  ((ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := s + 1) (a := k) Fact.out
    (Nat.succ_pos s)).mpr hk).unit

/-- The gamma values on the dense range, as a function on the subtype. -/
private noncomputable def moritaGammaPre (p : ℕ) [Fact p.Prime]
    (x : {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)}) : PadicInt p :=
  moritaGammaNat p (Function.invFun ((↑) : ℕ → PadicInt p) x.val)

/-- The range inclusion has dense range. -/
private lemma denseRange_subtype_val (p : ℕ) [Fact p.Prime] :
    DenseRange (Subtype.val :
      {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)} → PadicInt p) := by
  have h_range : Set.range (Subtype.val :
      {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)} → PadicInt p) =
      Set.range ((↑) : ℕ → PadicInt p) := by
    ext y
    simp only [Set.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · rintro ⟨n, rfl⟩
      exact ⟨⟨_, Set.mem_range_self n⟩, rfl⟩
  intro x
  rw [h_range]
  exact PadicInt.denseRange_natCast x

/-- The continuous extension of the gamma values to all of `PadicInt p`. -/
private noncomputable def moritaGammaExtend (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) :
    PadicInt p → PadicInt p :=
  IsDenseInducing.extend
    (IsUniformInducing.isDenseInducing isUniformEmbedding_subtype_val.isUniformInducing
      (denseRange_subtype_val p))
    (moritaGammaPre p)

private lemma uniformContinuous_moritaGammaExtend (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    UniformContinuous (moritaGammaExtend p hp2) :=
  uniformContinuous_uniformly_extend isUniformEmbedding_subtype_val.isUniformInducing
    (denseRange_subtype_val p) (uniformContinuous_moritaGammaPre p hp2)

private lemma moritaGammaExtend_coe (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) :
    moritaGammaExtend p hp2 ((n : ℕ) : PadicInt p) = moritaGammaNat p n := by
  have h1 := uniformly_extend_of_ind isUniformEmbedding_subtype_val.isUniformInducing
    (denseRange_subtype_val p) (uniformContinuous_moritaGammaPre p hp2)
    (⟨((n : ℕ) : PadicInt p), Set.mem_range_self n⟩ :
      {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)})
  rw [moritaGammaPre_eq _ _ n rfl] at h1
  exact h1

/-- For every odd prime, Morita's finite p-adic gamma values have a unique continuous,
unit-valued extension to the p-adic integers.

Source: Y. Morita, "A p-adic analogue of the Γ-function", J. Fac. Sci. Univ. Tokyo Sect. IA
Math. 22 (1975), 255–266. The definition and extension theorem are reproduced in
arXiv:2307.08940, arXiv:2307.10000, arXiv:2307.11982, arXiv:2310.15207, and arXiv:2311.03259.

Proves `Wanted` entry `existsUnique_moritaPadicGamma`.
-/
theorem existsUnique_moritaPadicGamma (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃! Γ : C(PadicInt p, PadicInt p), IsMoritaPadicGamma p Γ := by
  have hGn : ∀ n : ℕ, moritaGammaExtend p hp ((n : ℕ) : PadicInt p) = moritaGammaNat p n :=
    fun n => moritaGammaExtend_coe p hp n
  have hΓcont : Continuous (moritaGammaExtend p hp) :=
    (uniformContinuous_moritaGammaExtend p hp).continuous
  have hG0 : moritaGammaExtend p hp 0 = 1 := by
    have h0val := moritaGammaExtend_coe p hp 0
    rw [Nat.cast_zero] at h0val
    exact h0val.trans (moritaGammaNat_zero p)
  have hnorm : ∀ x : PadicInt p, ‖moritaGammaExtend p hp x‖ = 1 := by
    have hcont : Continuous (fun x : PadicInt p => ‖moritaGammaExtend p hp x‖) :=
      hΓcont.norm
    have heq : (fun x : PadicInt p => ‖moritaGammaExtend p hp x‖) = fun _ => 1 := by
      apply Continuous.ext_on PadicInt.denseRange_natCast hcont continuous_const
      rintro x ⟨n, rfl⟩
      change ‖moritaGammaExtend p hp ((n : ℕ) : PadicInt p)‖ = 1
      rw [hGn n]
      exact norm_moritaGammaNat p n
    intro x
    exact congrFun heq x
  have hGunit : ∀ x : PadicInt p, IsUnit (moritaGammaExtend p hp x) := by
    intro x
    rw [PadicInt.isUnit_iff]
    exact hnorm x
  refine ⟨⟨moritaGammaExtend p hp, hΓcont⟩, ⟨hG0, fun n _ => hGn n, hGunit⟩, ?_⟩
  intro Γ₂ hΓ₂
  apply ContinuousMap.ext
  intro x
  have hfun : (Γ₂ : PadicInt p → PadicInt p) = moritaGammaExtend p hp := by
    apply Continuous.ext_on PadicInt.denseRange_natCast Γ₂.continuous hΓcont
    rintro y ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero]
      rw [hΓ₂.1, hG0]
    · rw [hΓ₂.2.1 n hn, hGn n]
  exact congrFun hfun x

end MetaMathlibExt
