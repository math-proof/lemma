import Mathlib
import Initialize.Tactic.Attr.Basic
open Order PrimeSpectrum


namespace FiniteMorphismDimension

/--
[PrimeSpectrum.comap_strictMono_of_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiniteMorphismDimension.lean)
-/
@[path]
lemma PrimeSpectrum.comap_strictMono_of_isIntegral
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A] :
-- imply
  StrictMono (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  intro p q hpq
  have hpq' : p.asIdeal < q.asIdeal := hpq
  obtain ⟨hle, x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp hpq'
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxq, hxp⟩
    (Algebra.IsIntegral.isIntegral x)

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[ringKrullDim_le_of_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiniteMorphismDimension.lean)
-/
@[path]
lemma ringKrullDim_le_of_integral
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A] :
-- imply
  ringKrullDim A ≤ ringKrullDim B :=
-- proof
  krullDim_le_of_strictMono _ PrimeSpectrum.comap_strictMono_of_isIntegral

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[exists_lift_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiniteMorphismDimension.lean)
-/
@[path]
lemma exists_lift_chain
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A]
  {n : ℕ}
  {f : Fin (n + 1) → PrimeSpectrum B}
-- given
  (hinj : Function.Injective (algebraMap B A))
  (hf : ∀ i : Fin n, f i.castSucc < f i.succ) :
-- imply
  ∃ g : Fin (n + 1) → PrimeSpectrum A, (∀ i, PrimeSpectrum.comap (algebraMap B A) (g i) = f i) ∧ (∀ i : Fin n, g i.castSucc < g i.succ) := by
-- proof
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) :=
    RingHom.IsIntegral.comap_surjective (Algebra.isIntegral_def.mp inferInstance) hinj
  induction n with
  | zero =>
    obtain ⟨q, hq⟩ := hsurj (f 0)
    exact ⟨fun _ => q, fun i => by fin_cases i; exact hq, fun i => by fin_cases i⟩
  | succ n ih =>
    have hf' : ∀ i : Fin n, (f ∘ Fin.castSucc) i.castSucc < (f ∘ Fin.castSucc) i.succ :=
      fun i => hf i.castSucc
    obtain ⟨g', hg'_comap, hg'_strict⟩ := ih (f ∘ Fin.castSucc) hf'
    have hle : (g' (Fin.last n)).asIdeal.comap (algebraMap B A) ≤
      (f (Fin.last (n + 1))).asIdeal := by
      have h := congr_arg PrimeSpectrum.asIdeal (hg'_comap (Fin.last n))
      simp only [Function.comp, PrimeSpectrum.comap_asIdeal] at h
      rw [h]; exact le_of_lt (hf (Fin.last n))
    obtain ⟨Q, hQ_ge, hQ_prime, hQ_comap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral
        (f (Fin.last (n + 1))).asIdeal (g' (Fin.last n)).asIdeal hle
    let qLast : PrimeSpectrum A := ⟨Q, hQ_prime⟩
    refine ⟨Fin.snoc g' qLast, ?_, ?_⟩
    ·
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact PrimeSpectrum.ext hQ_comap
      · intro j; simp only [Fin.snoc_castSucc]; exact hg'_comap j
    ·
      intro i
      refine Fin.lastCases ?_ ?_ i
      ·
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last]
        refine lt_of_le_of_ne hQ_ge ?_
        intro heq
        have h1 : PrimeSpectrum.comap (algebraMap B A) qLast = f (Fin.last (n + 1)) :=
          PrimeSpectrum.ext hQ_comap
        have h2 := hg'_comap (Fin.last n)
        simp only [Function.comp] at h2
        have h3 : f (Fin.last (n + 1)) = f (Fin.castSucc (Fin.last n)) := by
          rw [← h1, ← h2, heq]
        exact absurd h3.symm (ne_of_lt (hf (Fin.last n)))
      ·
        intro j; simp only [Fin.snoc_castSucc, Fin.succ_castSucc]; exact hg'_strict j

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[ringKrullDim_ge_of_injective_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiniteMorphismDimension.lean)
-/
@[path]
lemma ringKrullDim_ge_of_injective_integral
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Algebra.IsIntegral B A]
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  ringKrullDim B ≤ ringKrullDim A := by
-- proof
  unfold ringKrullDim
  apply iSup_le
  intro chain_B
  obtain ⟨g, _, hg_strict⟩ := exists_lift_chain hinj chain_B.length chain_B.toFun chain_B.step
  exact le_iSup_of_le ⟨chain_B.length, g, hg_strict⟩ le_rfl

end FiniteMorphismDimension

namespace FiniteMorphismDimension

/--
[ringKrullDim_eq_of_injective_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiniteMorphismDimension.lean)
-/
@[path]
lemma ringKrullDim_eq_of_injective_finite
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  ringKrullDim A = ringKrullDim B := by
-- proof
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  exact le_antisymm ringKrullDim_le_of_integral (ringKrullDim_ge_of_injective_integral hinj)

end FiniteMorphismDimension


-- created on 2026-10-23
