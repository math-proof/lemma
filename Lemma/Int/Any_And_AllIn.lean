import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[PadicInt_exists_intermediateField_finiteDimensional_forall_algHom_apply_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PadicInt_exists_intermediateField_finiteDimensional_forall_algHom_apply_mem.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime]
  (H : Type) [CommRing H] [Algebra ℤ_[p] H] [Module.Finite ℤ_[p] H] :
  -- imply
  ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] L ∧ ∀ (f : AlgHom ℤ_[p] H (PadicAlgCl p)) (h : H), f h ∈ L := by
  -- proof
  classical
  obtain ⟨S, hS⟩ := (Module.finite_def.mp (inferInstance : Module.Finite ℤ_[p] H))
  let P : H → Polynomial (PadicAlgCl p) := fun s => (minpoly ℤ_[p] s).map (algebraMap ℤ_[p] (PadicAlgCl p))
  let R : Set (PadicAlgCl p) := ⋃ s ∈ (S : Set H), (((P s).roots.toFinset : Finset _) : Set (PadicAlgCl p))
  have hRfin : R.Finite := Set.Finite.biUnion S.finite_toSet (fun s _ => Finset.finite_toSet _)
  let _ : Finite R := hRfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[p] R, ?_, ?_⟩
  ·
    apply IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]) x).isIntegral)
  ·
    intro f h
    have hint : ∀ s : H, IsIntegral ℤ_[p] s := fun s => Algebra.IsIntegral.isIntegral s
    have hmem : ∀ s ∈ S, f s ∈ IntermediateField.adjoin ℚ_[p] R := by
      intro s hs
      apply IntermediateField.subset_adjoin
      simp only [R, Set.mem_iUnion, Finset.mem_coe, Multiset.mem_toFinset]
      refine ⟨s, hs, ?_⟩
      have hne : P s ≠ 0 := ((minpoly.monic (hint s)).map _).ne_zero
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map,
        ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have htop : h ∈ Submodule.span ℤ_[p] (S : Set H) := by
      rw [hS]
      trivial
    induction htop using Submodule.span_induction with
    | mem x hx => apply hmem x hx
    | zero =>
      rw [map_zero]
      apply zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      apply add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
      apply mul_mem (IntermediateField.algebraMap_mem _ _) hx


-- created on 2026-10-20
