import Mathlib
import Initialize.Tactic.Attr.Basic
import Definitions.Def_NumberField_ArchimedeanIdeleModule
open NumberField
open scoped NumberField.InfPlaceDecomp


/-- ported from external source -/
@[path]
private lemma main
  [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  {i : E}
  {v : InfinitePlace K}
-- given
  (hi : i ^ 2 = -1)
  (g : K ≃ₐ[E] K)
  (hg : g ∈ NumberField.InfPlaceDecomp.decomp E K v) :
-- imply
  g = 1 := by
  classical
    by_cases hunr : InfinitePlace.IsUnramified E v
    ·
      have hbot := hunr.stabilizer_eq_bot
      have hg' : g ∈ MulAction.stabilizer (K ≃ₐ[E] K) v := hg
      rw [hbot] at hg'
      exact Subgroup.mem_bot.1 hg'
    ·
      exfalso
      obtain ⟨-, hvR⟩ := InfinitePlace.not_isUnramified_iff.1 hunr
      set w := v.comap (algebraMap E K) with hw
      have hreal : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hvR
      have hconj : ComplexEmbedding.conjugate w.embedding = w.embedding := ComplexEmbedding.isReal_iff.1 hreal
      have h2 : starRingEnd ℂ (w.embedding i) = w.embedding i := by
-- proof
        simpa [ComplexEmbedding.conjugate_coe_eq] using RingHom.congr_fun hconj i
      have h1 : (w.embedding i) ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
      have hre : ((w.embedding i).re : ℂ) = w.embedding i := Complex.conj_eq_iff_re.1 h2
      rw [← hre, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_neg, Complex.ofReal_inj] at h1
      nlinarith [sq_nonneg (w.embedding i).re]


-- created on 2026-10-23
