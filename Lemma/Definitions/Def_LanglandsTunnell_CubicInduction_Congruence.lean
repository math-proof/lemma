import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Congruence

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

def congruenceK1 (c : ℕ) : Set (GL (Fin 3) (v.adicCompletion K)) :=
  {k | k ∈ localMaximalCompact3 R K v ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ))}

theorem mem_congruenceK1_iff {c : ℕ} {k : GL (Fin 3) (v.adicCompletion K)} :
    k ∈ congruenceK1 R K v c ↔
      k ∈ localMaximalCompact3 R K v ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ)) :=
  Iff.rfl

theorem mem_localMaximalCompact3_of_mem_congruenceK1 {c : ℕ} {k : GL (Fin 3) (v.adicCompletion K)}
    (hk : k ∈ congruenceK1 R K v c) : k ∈ localMaximalCompact3 R K v :=
  hk.1

theorem congruenceK1_antitone {c c' : ℕ} (h : c ≤ c') :
    congruenceK1 R K v c' ⊆ congruenceK1 R K v c := by
  intro k hk
  obtain ⟨h0, h1, h2, h3⟩ := hk
  have hle : WithZero.exp (-(c' : ℤ)) ≤ WithZero.exp (-(c : ℤ)) :=
    WithZero.exp_le_exp.mpr (by omega)
  exact ⟨h0, h1.trans hle, h2.trans hle, h3.trans hle⟩

theorem one_mem_congruenceK1 (c : ℕ) : (1 : GL (Fin 3) (v.adicCompletion K)) ∈ congruenceK1 R K v c := by
  refine ⟨one_mem _, ?_, ?_, ?_⟩ <;> simp

end Congruence

end LanglandsTunnell.CubicInduction
