import Mathlib
import sympy.Basic


/--
[isSMulRegular_iff_of_free](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_isSMulRegular_iff_of_free.lean)
-/
@[path]
private lemma main
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M]
  {r : R} :
-- imply
  IsSMulRegular M r ↔ IsSMulRegular R r := by
-- proof
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  constructor
  · intro H m n h
    have i : I := Nonempty.some inferInstance
    have := @H (m • b i) (n • b i) (by simp_all [← mul_smul])
    simpa using congr(b.repr $this i)
  · intro H m n h
    apply b.repr.injective
    ext i
    replace h := congr(b.repr $h i)
    simp only [map_smul] at h
    exact H h


-- created on 2026-10-05
