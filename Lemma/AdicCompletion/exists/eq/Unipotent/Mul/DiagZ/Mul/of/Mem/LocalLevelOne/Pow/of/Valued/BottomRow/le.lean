import Mathlib
import Lemma.AdicCompletion.Support.AdelicDock

open IsDedekindDomain NumberField AdicCompletion

/--
[AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le.lean)
-/
@[path]
private lemma main
-- given
  [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {ϖ : v.adicCompletionIntegers F} {m : ℕ}
  {g : GL (Fin 2) (v.adicCompletion F)} (hπ : (ϖ : v.adicCompletion F) ≠ 0)
  (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (hm : 1 ≤ m)
  (hc : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ≤ WithZero.exp (-(m : ℤ)))
  (hd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 - 1) ≤ WithZero.exp (-(m : ℤ))) :
-- imply
  ∃ (x : v.adicCompletion F) (n : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ AdelicDock.localLevelOne (𝓞 F) F v (v.asIdeal ^ m) ∧
      g = unipotent F v x * diagZ F v (ϖ : v.adicCompletion F) hπ n * k ∧
      Valued.v g.val.det = WithZero.exp (-n) := by
-- proof
  have hBm : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v = WithZero.exp (-(m : ℤ)) :=
    AdelicLevel.idealBound_pow F v m
  have hB : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v < 1 := by
    rw [hBm, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  obtain ⟨⟨x, n, k, hk, hg, hdet⟩⟩ := structure_lemma F v ϖ hπ hϖ m hB g
    (hBm ▸ hc) (hBm ▸ hd)
  exact ⟨x, n, k, hk, hg, hdet⟩


-- created on 2026-10-09
