/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LaplaceQPolynomial.lean -/


import Def.NumberTheory.LaplaceQPolynomial


namespace MetaMathlibExt

/-- Auxiliary iteration carrying the pair `(Q n, Q (n + 1))` for the positive
witness. Base `(1, X)`; step `(a, b) ↦ (b, X * b + (n + 2) • a)`.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
noncomputable def Qpair : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (1, Polynomial.X)
  | Nat.succ n => ((Qpair n).2, Polynomial.X * (Qpair n).2 + (n + 2) • (Qpair n).1)

/-- Positive-witness Q-family: first projection of `Qpair`.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
noncomputable def Qwit : ℕ → Polynomial ℤ := fun n => (Qpair n).1

/-- Positive-witness P-family: `P 0 = 0` and
`P (n + 1) = Q (n + 1) - derivative (Q n)`.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
noncomputable def Pwit : ℕ → Polynomial ℤ
  | 0 => 0
  | Nat.succ n => Qwit (Nat.succ n) - Polynomial.derivative (Qwit n)

/-- Constant-zero P-family for the negative witness.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
noncomputable def Pneg : ℕ → Polynomial ℤ := fun _ => 0

/-- Constant-one Q-family for the negative witness.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998. -/
noncomputable def Qneg : ℕ → Polynomial ℤ := fun _ => 1

end MetaMathlibExt
