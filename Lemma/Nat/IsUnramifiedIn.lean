import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq.lean)
-/
@[path]
private lemma main
  (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  {p : ℕ} (hp : p.Prime)
  (hζ : (primitiveRoots p E).Nonempty)
  (u : E) (α : M) (hα : α ^ p = algebraMap E M u)
  (hgen : IntermediateField.adjoin E {α} = ⊤)
  (w : NumberField.InfinitePlace E)
  (hb : w.IsReal → ∃ b : w.Completion, algebraMap E w.Completion u = b ^ p) :
  -- imply
  w.IsUnramifiedIn M := by
  -- proof
  classical
  intro w' hw'
  rw [NumberField.InfinitePlace.isUnramified_iff]
  if hwc : w.IsComplex then
    right
    rw [hw']
    apply hwc
  else
    left
    have hw : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hwc
    obtain ⟨ζ, hζ⟩ := hζ
    have hprim : IsPrimitiveRoot ζ p := (mem_primitiveRoots hp.pos).mp hζ
    have hp2 : p = 2 := by
      by_contra hne
      have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hne)
      have h0 := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hlt hprim
      have hpos : 0 < NumberField.InfinitePlace.nrRealPlaces E := Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
      omega
    subst hp2
    obtain ⟨b, hb⟩ := hb hw
    set φ : M →+* ℂ := w'.embedding with hφ
    set ψ : E →+* ℂ := φ.comp (algebraMap E M) with hψ
    have hψw : NumberField.InfinitePlace.mk ψ = NumberField.InfinitePlace.mk w.embedding := by
      rw [NumberField.InfinitePlace.mk_embedding, hψ, ← NumberField.InfinitePlace.comap_mk, hφ, NumberField.InfinitePlace.mk_embedding, hw']
    have hwr : NumberField.ComplexEmbedding.IsReal w.embedding := NumberField.InfinitePlace.isReal_iff.mp hw
    have hcases := NumberField.InfinitePlace.mk_eq_iff.mp hψw
    have hψreal : NumberField.ComplexEmbedding.IsReal ψ := by
      obtain h | h := hcases
      ·
        rw [h]
        apply hwr
      ·
        rw [← NumberField.ComplexEmbedding.isReal_conjugate_iff, h]
        apply hwr
    have hwu : ∃ r : ℝ, w.embedding u = (r : ℂ) ^ 2 := by
      have h1 : NumberField.InfinitePlace.Completion.extensionEmbedding w (algebraMap E w.Completion u) = (NumberField.InfinitePlace.Completion.extensionEmbedding w b) ^ 2 := by
        rw [hb, map_pow]
      rw [show algebraMap E w.Completion u = (((WithAbs.equiv w.1).symm u : WithAbs w.1) : w.Completion) from rfl, NumberField.InfinitePlace.Completion.extensionEmbedding_coe] at h1
      simp only [RingEquiv.apply_symm_apply] at h1
      refine ⟨NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw b, ?_⟩
      rw [h1, NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    obtain ⟨r, hr⟩ := hwu
    have hψu : ψ u = (r : ℂ) ^ 2 := by
      obtain h | h := hcases
      ·
        rw [h, hr]
      ·
        have h2 : starRingEnd ℂ (ψ u) = (r : ℂ) ^ 2 := by
          rw [← NumberField.ComplexEmbedding.conjugate_coe_eq, h, hr]
        have h3 := congrArg (starRingEnd ℂ) h2
        rwa [Complex.conj_conj, map_pow, Complex.conj_ofReal] at h3
    have hφα : starRingEnd ℂ (φ α) = φ α := by
      have hsq : (φ α) ^ 2 = (r : ℂ) ^ 2 := by
        rw [← map_pow, hα, ← hψu]
        rfl
      obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
      ·
        rw [h, Complex.conj_ofReal]
      ·
        rw [h, map_neg, Complex.conj_ofReal]
    let _ : Algebra E ℂ := ψ.toAlgebra
    have hcomm : ∀ e : E, starRingEnd ℂ (ψ e) = ψ e := fun e => RingHom.congr_fun hψreal e
    let φ₁ : M →ₐ[E] ℂ := AlgHom.mk φ fun e => rfl
    let φ₂ : M →ₐ[E] ℂ := AlgHom.mk ((starRingEnd ℂ).comp φ) hcomm
    have halg : IsAlgebraic E α := Algebra.IsAlgebraic.isAlgebraic α
    have hadj : Algebra.adjoin E {α} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg, hgen]
      rfl
    have heq : φ₂ = φ₁ := AlgHom.ext_of_adjoin_eq_top hadj fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      apply hφα
    rw [NumberField.InfinitePlace.isReal_iff]
    show NumberField.ComplexEmbedding.IsReal φ
    ext x
    apply AlgHom.congr_fun heq x


-- created on 2026-10-20
