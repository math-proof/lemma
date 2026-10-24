import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[PrimeSpectrum_apply_eq_apply_of_forall_le_of_connectedSpace](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PrimeSpectrum_apply_eq_apply_of_forall_le_of_connectedSpace.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsNoetherianRing R] [ConnectedSpace (PrimeSpectrum R)]
  {α : Type v} (φ : PrimeSpectrum R → α)
  (h : ∀ p q : PrimeSpectrum R, p ≤ q → φ p = φ q) (p q : PrimeSpectrum R) :
  -- imply
  φ p = φ q := by
  -- proof
  classical
  set S : Set (PrimeSpectrum R) := {x | φ x = φ p} with hS
  have key : ∀ T ∈ irreducibleComponents (PrimeSpectrum R), (T ∩ S).Nonempty → T ⊆ S := by
    intro T hT ⟨y, hyT, hyS⟩ x hxT
    have hirr : IsIrreducible T := hT.1
    have hcl : IsClosed T := isClosed_of_mem_irreducibleComponents T hT
    obtain ⟨η, hη⟩ := QuasiSober.sober hirr hcl
    have hηy : η ⤳ y := hη.specializes hyT
    have hηx : η ⤳ x := hη.specializes hxT
    rw [← PrimeSpectrum.le_iff_specializes] at hηy hηx
    have h1 : φ η = φ y := h η y hηy
    have h2 : φ η = φ x := h η x hηx
    show φ x = φ p
    rw [← h2, h1]; apply hyS
  have hfin : (irreducibleComponents (PrimeSpectrum R)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hSeq : S = ⋃ T ∈ {T ∈ irreducibleComponents (PrimeSpectrum R) | (T ∩ S).Nonempty}, T := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    ·
      intro hx
      exact ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ⟨x, mem_irreducibleComponent, hx⟩⟩, mem_irreducibleComponent⟩
    ·
      rintro ⟨T, ⟨hT, hne⟩, hxT⟩
      apply key T hT hne hxT
  have hScl : IsClosed S := by
    rw [hSeq]
    refine Set.Finite.isClosed_biUnion (hfin.subset (fun T hT => hT.1)) ?_
    intro T hT
    apply isClosed_of_mem_irreducibleComponents T hT.1
  have hCeq : Sᶜ = ⋃ T ∈ {T ∈ irreducibleComponents (PrimeSpectrum R) | ¬ (T ∩ S).Nonempty}, T := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Set.mem_compl_iff]
    constructor
    ·
      intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩, mem_irreducibleComponent⟩
      intro hne
      apply hx (key _ (irreducibleComponent_mem_irreducibleComponents x) hne mem_irreducibleComponent)
    ·
      rintro ⟨T, ⟨hT, hne⟩, hxT⟩ hx
      apply hne ⟨x, hxT, hx⟩
  have hCcl : IsClosed Sᶜ := by
    rw [hCeq]
    refine Set.Finite.isClosed_biUnion (hfin.subset (fun T hT => hT.1)) ?_
    intro T hT
    apply isClosed_of_mem_irreducibleComponents T hT.1
  have hclopen : IsClopen S := ⟨hScl, isClosed_compl_iff.mp hCcl⟩
  have huniv : S = Set.univ := hclopen.eq_univ ⟨p, rfl⟩
  have hq : q ∈ S := by rw [huniv]; trivial
  refine hq.symm


-- created on 2026-10-20
