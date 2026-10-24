/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/AdjoinRoot/LocalMaximal.lean -/


import Mathlib.Algebra.Field.ZMod
import sympy.atlas.RingTheory.AdjoinRoot.LocalMaximal
import Lemma.Polynomial.AdjoinRoot.LocalMaximal


open Polynomial

variable {A : Type*} [CommRing A] [IsLocalRing A]

-- The kernel identity is directly usable.
example (I : Ideal A) :
    Ideal.comap (Polynomial.mapRingHom (Ideal.Quotient.mk I)) ⊥ =
      Ideal.map Polynomial.C I :=
  Polynomial.comap_mapRingHom_bot_eq_map_C_ker I

-- The backward direction turns an irreducible factor into a maximal ideal.
example (g q : A[X])
    (hirr : Irreducible
      (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))
    (hdvd : (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣
      (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
    (Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ⊔
      Ideal.span {AdjoinRoot.mk g q}).IsMaximal :=
  AdjoinRoot.is_maximal_of_irreducible_factor g q hirr hdvd

-- For monic `g`, integrality is automatic and the classification applies.
example (g : A[X]) (hg : g.Monic) (m : Ideal (AdjoinRoot g)) :
    m.IsMaximal ↔
      ∃ q : A[X],
        Irreducible
          (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
          (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣
            (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
          m = Ideal.map (algebraMap A (AdjoinRoot g))
            (IsLocalRing.maximalIdeal A) ⊔
            Ideal.span {AdjoinRoot.mk g q} := by
  have := hg.finite_adjoinRoot
  exact AdjoinRoot.is_maximal_iff_irreducible_factor g m

-- Concrete finite-field regression: monic reducible `X * (X - 1)` over `ZMod 5`.
noncomputable example [Fact (Nat.Prime 5)] :
    let g : (ZMod 5)[X] := X * (X - C 1)
    (Ideal.span {AdjoinRoot.root g} : Ideal (AdjoinRoot g)).IsMaximal := by
  let g : (ZMod 5)[X] := X * (X - C 1)
  have hg : g.Monic := monic_X.mul (monic_X_sub_C 1)
  let _ : Field ((ZMod 5) ⧸ IsLocalRing.maximalIdeal (ZMod 5)) :=
    Ideal.Quotient.field _
  apply (AdjoinRoot.is_maximal_iff_irreducible_factor_of_monic
    g hg (Ideal.span {AdjoinRoot.root g})).2
  refine ⟨X, ?_, ?_, ?_⟩
  · simpa using (irreducible_X : Irreducible
      (X : ((ZMod 5) ⧸ IsLocalRing.maximalIdeal (ZMod 5))[X]))
  · simp [g]
  · simp [IsLocalRing.maximalIdeal_eq_bot, AdjoinRoot.mk_X]
