import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[Algebra_exists_faithfullyFlat_finitePresentation_forall_pow_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_faithfullyFlat_finitePresentation_forall_pow_eq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {ι : Type} [Finite ι]
  {m : ℕ}
  {u : ι → Rˣ}
-- given
  (hm : 0 < m) :
-- imply
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
    Module.FaithfullyFlat R R' ∧ Algebra.FinitePresentation R R' ∧
    ∃ v : ι → R'ˣ, ∀ i, (v i : R') ^ m = algebraMap R R' (u i) := by
-- proof
  classical
  obtain hR | hR := subsingleton_or_nontrivial R
  ·
    refine ⟨R, inferInstance, inferInstance, Module.FaithfullyFlat.self R,
      Algebra.FinitePresentation.self R, fun _ => 1, fun i => Subsingleton.elim _ _⟩
  ·
    suffices h : ∀ (α : Type) [Finite α] (w : α → Rˣ),
        ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
          Nontrivial R' ∧ Module.FaithfullyFlat R R' ∧ Algebra.FinitePresentation R R' ∧
          ∃ v : α → R'ˣ, ∀ i, (v i : R') ^ m = algebraMap R R' (w i) by
      obtain ⟨R', _, _, -, hff, hfp, v, hv⟩ := h ι u
      refine ⟨R', _, _, hff, hfp, v, hv⟩
    intro α hα
    refine @Finite.induction_empty_option
      (fun α => ∀ w : α → Rˣ, ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
        Nontrivial R' ∧ Module.FaithfullyFlat R R' ∧ Algebra.FinitePresentation R R' ∧
        ∃ v : α → R'ˣ, ∀ i, (v i : R') ^ m = algebraMap R R' (w i)) ?_ ?_ ?_ α hα
    ·
      intro α β e h w
      obtain ⟨R', _, _, hnt, hff, hfp, v, hv⟩ := h (w ∘ e)
      refine ⟨R', _, _, hnt, hff, hfp, fun b => v (e.symm b), fun b => ?_⟩
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hv (e.symm b)
    ·
      intro w
      refine ⟨R, inferInstance, inferInstance, hR, Module.FaithfullyFlat.self R,
        Algebra.FinitePresentation.self R, fun i => i.elim, fun i => i.elim⟩
    ·
      intro α _ ih w
      obtain ⟨R₁, _, _, hnt, hff, hfp, v, hv⟩ := ih (fun a => w (some a))
      let _ : Nontrivial R₁ := hnt
      let _ : Module.FaithfullyFlat R R₁ := hff
      let _ : Algebra.FinitePresentation R R₁ := hfp
      let a : R₁ := algebraMap R R₁ (w none)
      let f : Polynomial R₁ := Polynomial.X ^ m - Polynomial.C a
      have hf : f.Monic := Polynomial.monic_X_pow_sub_C a hm.ne'
      have hdeg : f.natDegree = m := Polynomial.natDegree_X_pow_sub_C
      let pb := AdjoinRoot.powerBasis' hf
      let _ : Module.Free R₁ (AdjoinRoot f) := Module.Free.of_basis pb.basis
      let _ : Module.Finite R₁ (AdjoinRoot f) := Module.Finite.of_basis pb.basis
      let _ : Nontrivial (AdjoinRoot f) := by
        have hdim : pb.dim = m := by
          rw [AdjoinRoot.powerBasis'_dim, hdeg]
        apply nontrivial_of_ne (pb.basis ⟨0, by omega⟩) 0 (pb.basis.ne_zero _)
      let _ : Module.FaithfullyFlat R₁ (AdjoinRoot f) := inferInstance
      let _ : Algebra.FinitePresentation R₁ (AdjoinRoot f) := inferInstance
      have hroot : (AdjoinRoot.root f) ^ m = algebraMap R (AdjoinRoot f) (w none) := by
        have h0 := AdjoinRoot.eval₂_root f
        simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h0
        rw [h0, IsScalarTower.algebraMap_apply R R₁ (AdjoinRoot f), AdjoinRoot.algebraMap_eq]
      have hunit : IsUnit (AdjoinRoot.root f) := by
        rw [← isUnit_pow_iff hm.ne', hroot]
        apply (w none).isUnit.map _
      refine ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, Module.FaithfullyFlat.trans R R₁ _,
        Algebra.FinitePresentation.trans R R₁ _,
        fun o => o.elim hunit.unit (fun b => (v b).map (algebraMap R₁ (AdjoinRoot f)).toMonoidHom),
        fun o => ?_⟩
      cases o with
      | none =>
        show (hunit.unit : AdjoinRoot f) ^ m = _
        rw [IsUnit.unit_spec, hroot]
      | some b =>
        show (algebraMap R₁ (AdjoinRoot f) (v b : R₁)) ^ m = _
        rw [← map_pow, hv b, ← IsScalarTower.algebraMap_apply]


-- created on 2026-10-13
