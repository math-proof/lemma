import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[ValuationSubring_eq_zero_of_valuation_eval2_lt_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_eq_zero_of_valuation_eval2_lt_one.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {K : Type v} [Field K]
  (c : RingHom k K)
  (O : ValuationSubring K)
  {d : ℕ}
  (g : Fin d → K)
  (Q : MvPolynomial (Fin d) k)
  -- given
  (hc : ∀ x : k, c x ∈ O)
  (hg : ∀ i, g i ∈ O)
  (hind :
    let _ : Algebra k (IsLocalRing.ResidueField O) :=
      ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
    AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩))
  (hQ : O.valuation (Q.eval₂ c g) < 1) :
  -- imply
  Q = 0 := by
  -- proof
  classical
  let instAlg : Algebra k (IsLocalRing.ResidueField O) :=
    ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
  let cO : RingHom k ↥O := c.codRestrict O.toSubring hc
  let gO : Fin d → ↥O := fun j => ⟨g j, hg j⟩
  have hev : Q.eval₂ c g = algebraMap ↥O K (Q.eval₂ cO gO) := by
    rw [MvPolynomial.eval₂_comp_left]
    rfl
  rw [hev] at hQ
  have hmem : Q.eval₂ cO gO ∈ IsLocalRing.maximalIdeal ↥O := (O.valuation_lt_one_iff _).mpr hQ
  have hres : IsLocalRing.residue ↥O (Q.eval₂ cO gO) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [MvPolynomial.eval₂_comp_left] at hres
  rw [algebraicIndependent_iff] at hind
  apply hind Q
  rw [MvPolynomial.aeval_def]
  apply hres


-- created on 2026-10-20
