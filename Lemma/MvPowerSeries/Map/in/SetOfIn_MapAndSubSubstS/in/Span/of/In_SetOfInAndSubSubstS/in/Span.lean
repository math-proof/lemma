import Mathlib
import sympy.Basic
import Lemma.MvFormalGroup.NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.Int.P2MUtil

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

/--
[CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {R R' : Type} [CommRing R] [CommRing R']
  {X : FormalODModule p R}
  {J : Ideal (MvPowerSeries (Fin 2) R)}
  {ψ : R →+* R'}
  {w : MvPowerSeries (Fin 2) R}
-- given
  (hw : w ∈ {w : MvPowerSeries (Fin 2) R | w ∈ J ∧ MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈ Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) '' (J : Set (MvPowerSeries (Fin 2) R)))}) :
-- imply
  MvPowerSeries.map ψ w ∈ {w : MvPowerSeries (Fin 2) R' | w ∈ (J.map (MvPowerSeries.map ψ)) ∧
          MvPowerSeries.subst (X.map ψ).F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R')) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R'))) '' ((J.map (MvPowerSeries.map ψ)) : Set (MvPowerSeries (Fin 2) R')))} := by
  obtain ⟨hwJ, hwinv⟩ := hw
  refine ⟨Ideal.mem_map_of_mem _ hwJ, ?_⟩
  have hF : MvPowerSeries.HasSubst X.F.toPowerSeries := X.F.hasSubst_toPowerSeries
  have hXl : MvPowerSeries.HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have hXr : MvPowerSeries.HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have h1 : MvPowerSeries.map ψ (MvPowerSeries.subst X.F.toPowerSeries w) =
      MvPowerSeries.subst (X.map ψ).F.toPowerSeries (MvPowerSeries.map ψ w) := by
-- proof
    rw [MvPowerSeries.map_subst hF]
    rfl
  have h2 : MvPowerSeries.map ψ (MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w) =
      MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R'))
        (MvPowerSeries.map ψ w) := by
    rw [MvPowerSeries.map_subst hXl]
    congr 1
    funext l
    exact MvPowerSeries.map_X _ _
  have hle : Ideal.map (MvPowerSeries.map (σ := Fin 2 ⊕ Fin 2) ψ)
    (Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) ''
      (J : Set (MvPowerSeries (Fin 2) R)))) ≤
    Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R'))) ''
      ((J.map (MvPowerSeries.map ψ)) : Set (MvPowerSeries (Fin 2) R'))) := by
    rw [Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    apply Ideal.subset_span
    refine ⟨MvPowerSeries.map ψ j, Ideal.mem_map_of_mem _ hj, ?_⟩
    show MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R')) (MvPowerSeries.map ψ j) =
      MvPowerSeries.map ψ (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) j)
    rw [MvPowerSeries.map_subst hXr]
    congr 1
    funext l
    exact (MvPowerSeries.map_X _ _).symm
  rw [← h1, ← h2, ← map_sub]
  exact hle (Ideal.mem_map_of_mem _ hwinv)


-- created on 2026-10-23
