import Mathlib
import sympy.Basic
import Def.MathlibExtTest.NumberTheory.LaplaceQPolynomial


namespace MetaMathlibExt

/--
[Qwit_two_step_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LaplaceQPolynomial.lean)
-/
@[path]
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private lemma Qwit_two_step_add (n : ℕ) :
  Qwit (n + 2) = Polynomial.X * Qwit (n + 1) + (n + 2) • Qwit n :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Qwit_first_eq_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LaplaceQPolynomial.lean)
-/
@[path]
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private lemma Qwit_first_eq_add (n : ℕ) :
  Qwit (n + 1) = Pwit (n + 1) + Polynomial.derivative (Qwit n) := by
  have hP : Pwit (n + 1) = Qwit (n + 1) - Polynomial.derivative (Qwit n) := rfl
  rw [hP]
  exact (sub_add_cancel _ _).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[positive_witness_is_family](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LaplaceQPolynomial.lean)
-/
@[path]
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private lemma positive_witness_is_family :
  IsLaplaceQFamily Pwit Qwit := by
  unfold IsLaplaceQFamily
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk_eq : k = (k - 1) + 1 := by omega
  have hsub : (k - 1) + 1 - 1 = k - 1 := by omega
  have hadd : (k - 1) + 1 + 1 = (k - 1) + 2 := by omega
  refine ⟨?_, ?_⟩
  · rw [hk_eq, hsub]
    exact Qwit_first_eq_add (k - 1)
  · rw [hk_eq, hsub, hadd]
    exact Qwit_two_step_add (k - 1)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[negative_witness_fails](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LaplaceQPolynomial.lean)
-/
@[path]
at `k = 1`, hence fail the predicate.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
private lemma negative_witness_fails : ¬ IsLaplaceQFamily Pneg Qneg := by
  unfold IsLaplaceQFamily
  rintro ⟨_, hrec⟩
  have h1 := (hrec 1 le_rfl).1
  have e1 : Qneg 1 = (1 : Polynomial ℤ) := rfl
  have e2 : Pneg 1 = (0 : Polynomial ℤ) := rfl
  have e3 : Qneg (1 - 1) = (1 : Polynomial ℤ) := rfl
  rw [e1, e2, e3, Polynomial.derivative_one] at h1
  simp at h1

end MetaMathlibExt


-- created on 2026-10-23
