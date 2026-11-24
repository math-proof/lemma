module
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

lemma pgf_rgJoinMap_injective (n k : ℕ) :
    Function.Injective (pgf_rgJoinMap n k) := by
  intro d₁ d₂ h
  apply Subtype.ext
  apply pgf_joinFirst_injective n k
  simpa [pgf_rgJoinMap] using congrArg Subtype.val h

lemma pgf_rgJoinMap_surjective (n k : ℕ) :
    Function.Surjective (pgf_rgJoinMap n k) := by
  intro w
  obtain ⟨z, hz⟩ := pgf_decodeFirst_surjective n k w
  cases z with
  | inl u =>
      obtain ⟨j, hj⟩ := w.property.1 (Fin.last k)
      have hc := congrFun hz j
      simp only [pgf_decodeFirst, Function.comp_apply] at hc
      exact False.elim (Fin.castSucc_ne_last _ (hc.trans hj))
  | inr d =>
      have hz' : pgf_joinFirst d = w := by simpa [pgf_decodeFirst] using hz
      have hdjoin : IsSurjectiveRestrictedGrowthString (pgf_joinFirst d) := by
        rw [hz']
        exact w.property
      let d' : {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} :=
        ⟨d, (pgf_rg_join_iff d.1 d.2.1 d.2.2).1 hdjoin⟩
      refine ⟨d', ?_⟩
      apply Subtype.ext
      simpa [pgf_rgJoinMap] using hz'

end MetaMathlibExt
