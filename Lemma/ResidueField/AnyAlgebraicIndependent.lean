import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {K : Type v} [Field K]
  (c : RingHom k K)
  (O : ValuationSubring K)
  {d : ℕ}
  -- given
  (hc : ∀ x : k, c x ∈ O)
  (hd :
    let _ : Algebra k (IsLocalRing.ResidueField O) :=
      ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
    (d : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O)) :
  -- imply
  let _ : Algebra k (IsLocalRing.ResidueField O) :=
    ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
  ∃ (g : Fin d → K) (hg : ∀ i, g i ∈ O), AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩) := by
  -- proof
  let _ : Algebra k (IsLocalRing.ResidueField O) :=
    ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
  classical
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' k (IsLocalRing.ResidueField O)
  have hcard : (d : Cardinal) ≤ Cardinal.mk ι := by
    rw [hx.cardinalMk_eq_trdeg]
    apply hd
  have hemb : Nonempty (Fin d ↪ ι) := by
    rw [← Cardinal.lift_mk_le']
    simpa using hcard
  obtain ⟨e⟩ := hemb
  have hind : AlgebraicIndependent k (x ∘ e) := hx.1.comp e e.injective
  have hl : ∀ i, ∃ y : ↥O, IsLocalRing.residue ↥O y = x (e i) := fun i => IsLocalRing.residue_surjective _
  choose gO hgO using hl
  refine ⟨fun i => (gO i : K), fun i => (gO i).2, ?_⟩
  have : (fun i => IsLocalRing.residue ↥O ⟨(gO i : K), (gO i).2⟩) = x ∘ e := funext fun i => hgO i
  rw [this]
  apply hind


-- created on 2026-10-20
