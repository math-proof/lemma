import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ.lean)
-/
@[path]
private lemma main
    {T : Type} [TopologicalSpace T] {ι : Type} (W : ι → Set T) (hW : ∀ i, IsOpen (W i))
    (hcov : ⋃ i, W i = Set.univ) :
    topologicalKrullDim T = ⨆ i, topologicalKrullDim ↥(W i) := by
  classical
  apply le_antisymm
  ·
    show Order.krullDim (IrreducibleCloseds T) ≤ ⨆ i, Order.krullDim (IrreducibleCloseds ↥(W i))
    rw [Order.krullDim]
    refine iSup_le (fun p => ?_)
    obtain ⟨x, hx⟩ := (p 0).isIrreducible'.nonempty
    obtain ⟨i, hi⟩ : ∃ i, x ∈ W i := by
      have : x ∈ ⋃ i, W i := by rw [hcov]; trivial
      simpa only [Set.mem_iUnion] using this
    have hmono : Monotone p := p.monotone
    have hxj : ∀ j : Fin (p.length + 1), x ∈ (p j : Set T) := fun j => hmono (Fin.zero_le j) hx
    have hne : ∀ j : Fin (p.length + 1), (((p j : Set T)) ∩ W i).Nonempty := fun j => ⟨x, hxj j, hi⟩
    have key : ∀ k : Fin (p.length + 1), (p k : Set T) = closure ((p k : Set T) ∩ W i) := by
      intro k
      apply le_antisymm
      · exact subset_closure_inter_of_isPreirreducible_of_isOpen (p k).isIrreducible'.isPreirreducible (hW i) (hne k)
      · exact (p k).isClosed'.closure_subset_iff.2 Set.inter_subset_left
    let r : Fin (p.length + 1) → IrreducibleCloseds ↥(W i) := fun j =>
      { carrier := Subtype.val ⁻¹' (p j : Set T)
        isIrreducible' := ⟨⟨⟨x, hi⟩, hxj j⟩,
          ((p j).isIrreducible'.isPreirreducible).preimage (hW i).isOpenEmbedding_subtypeVal⟩
        isClosed' := (p j).isClosed'.preimage continuous_subtype_val }
    have hr_carrier : ∀ j, ((r j : Set ↥(W i))) = Subtype.val ⁻¹' (p j : Set T) := fun j => rfl
    have hstep : ∀ j : Fin p.length, r (Fin.castSucc j) < r j.succ := by
      intro j
      have hlt : p (Fin.castSucc j) < p j.succ := p.step j
      refine lt_of_le_of_ne ?_ ?_
      · intro y hy
        show (y : T) ∈ (p j.succ : Set T)
        exact (le_of_lt hlt) hy
      · intro heq
        apply ne_of_lt hlt
        have h1 : (Subtype.val : ↥(W i) → T) ⁻¹' (p (Fin.castSucc j) : Set T) = Subtype.val ⁻¹' (p j.succ : Set T) := by
          rw [← hr_carrier, ← hr_carrier, heq]
        have hsets : (p (Fin.castSucc j) : Set T) ∩ W i = (p j.succ : Set T) ∩ W i := by
          have := congrArg (fun A : Set ↥(W i) => (Subtype.val '' A)) h1
          simpa only [Subtype.image_preimage_coe, Set.inter_comm] using this
        apply IrreducibleCloseds.ext
        rw [key (Fin.castSucc j), key j.succ, hsets]
    let q : LTSeries (IrreducibleCloseds ↥(W i)) := { length := p.length, toFun := r, step := hstep }
    calc ((p.length : ℕ) : WithBot ℕ∞) = q.length := rfl
      _ ≤ Order.krullDim (IrreducibleCloseds ↥(W i)) := Order.LTSeries.length_le_krullDim q
      _ ≤ ⨆ i, Order.krullDim (IrreducibleCloseds ↥(W i)) := le_iSup (fun i => Order.krullDim (IrreducibleCloseds ↥(W i))) i
  · exact iSup_le (fun i => topologicalKrullDim_subspace_le T (W i))

-- created on 2026-10-20
