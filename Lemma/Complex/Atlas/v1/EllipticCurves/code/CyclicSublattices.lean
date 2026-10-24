import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.CyclicSublattices
open Complex


/--
[spanLattice_one_Ntau_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CyclicSublattices.lean)
-/
@[path]
lemma spanLattice_one_Ntau_sub
  {τ : ℂ}
  {N : ℕ}
-- given
  (hτ : 0 < τ.im)
  (hN : 0 < N) :
-- imply
  spanLattice 1 (↑N * τ) ≤ spanLattice 1 τ := by
-- proof
  have h1 : (1 : ℂ) ∈ spanLattice 1 τ :=
    AddSubgroup.subset_closure (Set.mem_insert _ _)
  have hτ : τ ∈ spanLattice 1 τ :=
    AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  simp only [spanLattice]
  apply (AddSubgroup.closure_le (spanLattice 1 τ)).2
  intro x hx
  obtain rfl | hx := Set.mem_insert_iff.mp hx
  · exact h1
  · rw [Set.mem_singleton_iff.mp hx, show (↑N : ℂ) * τ = (N : ℤ) • τ from by simp [zsmul_eq_mul]]
    exact (spanLattice 1 τ).zsmul_mem hτ N

/--
[spanLattice_N_taupk_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CyclicSublattices.lean)
-/
@[path]
lemma spanLattice_N_taupk_sub
  {τ : ℂ}
  {N : ℕ}
  {k : Fin N}
-- given
  (hτ : 0 < τ.im)
  (hN : 0 < N) :
-- imply
  spanLattice (↑N) (τ + ↑(k : ℕ)) ≤ spanLattice 1 τ := by
-- proof
  simp only [spanLattice]
  apply (AddSubgroup.closure_le (AddSubgroup.closure {1, τ})).2
  intro x hx
  obtain rfl | hx := Set.mem_insert_iff.mp hx
  · rw [show (↑N : ℂ) = (N : ℤ) • (1 : ℂ) from by simp [zsmul_eq_mul]]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_insert _ _)) N
  · rw [Set.mem_singleton_iff.mp hx, show (↑(k : ℕ) : ℂ) = ((k : ℕ) : ℤ) • (1 : ℂ) from by
    simp [zsmul_eq_mul]]
    exact AddSubgroup.add_mem _
      (AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_insert _ _)) (k : ℕ))

/--
[prime_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CyclicSublattices.lean)
-/
@[path]
lemma prime_mul_eq
  {a d N : ℕ}
-- given
  (hN : Nat.Prime N)
  (ha : 0 < a)
  (hd : 0 < d)
  (h : a * d = N) :
-- imply
  (a = 1 ∧ d = N) ∨ (a = N ∧ d = 1) := by
-- proof
  obtain ha1 | haN := hN.eq_one_or_self_of_dvd a ⟨d, h.symm⟩
  · subst ha1
    simp at h
    exact Or.inl ⟨rfl, h⟩
  · right
    refine ⟨haN, ?_⟩
    nlinarith [hN.one_lt]
/-- Classification of cyclic sublattices of prime index $p$ in $\mathbb{Z} + \mathbb{Z}\tau$:
they are exactly the $p+1$ lattices $\mathbb{Z} + \mathbb{Z}(p\tau)$ and
$\mathbb{Z}p + \mathbb{Z}(\tau + k)$ for $k = 0, 1, \ldots, p-1$. This parametrizes the
$p+1$ cyclic $p$-isogenies out of the complex torus $\mathbb{C}/(\mathbb{Z}+\mathbb{Z}\tau)$. -/


-- created on 2026-10-23
