/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/LatticePointEnumerator.lean -/


import Def.Geometry.LatticePointEnumerator
import Lemma.Set.LatticePointEnumerator
open LatticePointEnumerator

open scoped Pointwise

/-!
# Tests for lattice-point enumerators
-/


/-- Boundary: the origin lies in the integer lattice. -/
example (d : ℕ) : (0 : Fin d → ℝ) ∈ stdLattice d :=
  zero_mem_stdLattice d

/-- Boundary: the empty set enumerates to zero. -/
example (d : ℕ) (t : ℝ) : latticeEnumerator d ∅ t = 0 :=
  latticeEnumerator_empty d t

/-- Boundary: the translated empty set enumerates to zero. -/
example (d : ℕ) (t : ℝ) (x : Fin d → ℝ) :
    translatedLatticeEnumerator d ∅ t x = 0 :=
  translatedLatticeEnumerator_empty d t x

/-- Nonempty bounded set: the singleton at the origin is bounded. -/
example : Bornology.IsBounded ({0} : Set (Fin 2 → ℝ)) :=
  (Set.finite_singleton (0 : Fin 2 → ℝ)).isBounded

/-- Nonempty: the lattice-point set of the singleton is finite. -/
example :
    Set.Finite (latticePointSet 2 ({0} : Set (Fin 2 → ℝ)) 1) :=
  finite_latticePointSet 2 ({0} : Set (Fin 2 → ℝ)) 1
    (Set.finite_singleton (0 : Fin 2 → ℝ)).isBounded

/-- Nonempty: the source-domain point set is finite for a positive dilation. -/
example :
    Set.Finite
      (latticePointSetPos 2 ({0} : Set (Fin 2 → ℝ)) ⟨1, one_pos⟩) :=
  finite_latticePointSetPos 2 ({0} : Set (Fin 2 → ℝ)) ⟨1, one_pos⟩
    (Set.finite_singleton (0 : Fin 2 → ℝ)).isBounded

/-- Nonempty: concrete enumerator value for the singleton at the origin. -/
example : latticeEnumerator 2 ({0} : Set (Fin 2 → ℝ)) 1 = 1 := by
  have h0 : (0 : Fin 2 → ℝ) ∈ stdLattice 2 := zero_mem_stdLattice 2
  have hsmul : (1 : ℝ) • ({0} : Set (Fin 2 → ℝ)) = {0} := by simp
  unfold latticeEnumerator latticePointSet
  rw [hsmul, Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.mpr h0),
    Set.ncard_singleton]

/-- Source domain: concrete enumerator value at a positive dilation. -/
example : latticeEnumeratorPos 2 ({0} : Set (Fin 2 → ℝ))
    (Set.finite_singleton (0 : Fin 2 → ℝ)).isBounded ⟨1, one_pos⟩ = 1 := by
  have h0 : (0 : Fin 2 → ℝ) ∈ stdLattice 2 := zero_mem_stdLattice 2
  have hsmul : (⟨1, one_pos⟩ : {t : ℝ // 0 < t}).val • ({0} : Set (Fin 2 → ℝ)) =
      {0} := by simp
  unfold latticeEnumeratorPos latticeEnumerator latticePointSet
  rw [hsmul, Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.mpr h0),
    Set.ncard_singleton]

/-- Nonzero standard-basis vector lies in the integer lattice. -/
example : Pi.basisFun ℝ (Fin 2) 0 ∈ stdLattice 2 :=
  Submodule.subset_span (Set.mem_range_self 0)

/-- Half vector in dimension one is not in the integer lattice. -/
example : (fun _ : Fin 1 => (1 / 2 : ℝ)) ∉ stdLattice 1 := by
  rw [mem_stdLattice_iff]
  intro h
  obtain ⟨z, hz⟩ := h 0
  have h2 : (z : ℝ) * 2 = 1 := by rw [hz]; norm_num
  have h3 : z * 2 = 1 := by exact_mod_cast h2
  omega

/-- Translation-order regression at `P = {0}`, `t = 2`, `x = 1 / 2`: the unit
vector lies in dilate-after-translate but not in translate-after-dilate. -/
example : (fun _ : Fin 1 => (1 : ℝ)) ∈
    ((((2 : ℝ) • (({0} : Set (Fin 1 → ℝ)) + {(fun _ => (1 / 2 : ℝ))}))
      ∩ (stdLattice 1 : Set (Fin 1 → ℝ)))) ∧
    (fun _ : Fin 1 => (1 : ℝ)) ∉
      translatedLatticePointSet 1 ({0} : Set (Fin 1 → ℝ)) 2
        (fun _ => (1 / 2 : ℝ)) := by
  have h1mem : (fun _ : Fin 1 => (1 : ℝ)) ∈ stdLattice 1 := by
    have hbasis : Pi.basisFun ℝ (Fin 1) 0 ∈ stdLattice 1 :=
      Submodule.subset_span (Set.mem_range_self 0)
    have heq : (fun _ : Fin 1 => (1 : ℝ)) = Pi.basisFun ℝ (Fin 1) 0 := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [Pi.basisFun]
    rwa [heq]
  have hadd : (({0} : Set (Fin 1 → ℝ)) + {(fun _ => (1 / 2 : ℝ))}) =
      {(fun _ => (1 / 2 : ℝ))} := by simp
  have hpoint : (2 : ℝ) • (fun _ : Fin 1 => (1 / 2 : ℝ)) =
      (fun _ => (1 : ℝ)) := by
    funext i
    simp
  have hwrong : (2 : ℝ) • (({0} : Set (Fin 1 → ℝ)) +
      {(fun _ => (1 / 2 : ℝ))}) = {(fun _ => (1 : ℝ))} := by
    rw [hadd, Set.smul_set_singleton, hpoint]
  have hcorr : ((2 : ℝ) • ({0} : Set (Fin 1 → ℝ)) +
      {(fun _ => (1 / 2 : ℝ))}) = {(fun _ => (1 / 2 : ℝ))} := by simp
  constructor
  · rw [hwrong,
      Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.mpr h1mem)]
    exact Set.mem_singleton _
  · unfold translatedLatticePointSet
    rw [hcorr]
    intro h
    have hsingle := Set.mem_singleton_iff.mp h.1
    have h0 := congrFun hsingle 0
    norm_num at h0

