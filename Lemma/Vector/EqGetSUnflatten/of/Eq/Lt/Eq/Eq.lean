import Lemma.Vector.EqGetSUnflatten.of.Eq.Eq.Lt.Eq.Eq
open Vector


@[main]
private lemma main
  {v : List.Vector α (m * n)}
  {v' : List.Vector α (m' * n')}
  {i : ℕ}
-- given
  (h₀ : m = m')
  (h₁ : n = n')
  (h₂ : i < m)
  (h₄ : v ≃ v') :
-- imply
  v.unflatten[i] ≃ v'.unflatten[i] := by
-- proof
  apply EqGetSUnflatten.of.Eq.Eq.Lt.Eq.Eq
  repeat assumption
  .
    rfl
  ·
    assumption


-- created on 2025-07-15
