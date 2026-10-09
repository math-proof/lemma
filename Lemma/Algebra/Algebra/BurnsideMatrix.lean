import Mathlib
import sympy.Basic
import sympy.Algebra.Algebra.BurnsideMatrix

open BurnsideMatrix

/--
[burnsideSimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/BurnsideMatrix.lean)
-/
@[main]
private lemma simple
  [Field k]
-- given
  (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
  (h : ∀ W : Submodule k (Fin n → k),
    (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
  (hn : n ≠ 0) :
-- imply
  IsSimpleModule ↥A (Fin n → k) := by
-- proof
  apply burnsideSimple A h hn


/--
[burnside_commutant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/BurnsideMatrix.lean)
-/
@[main]
private lemma commutant
  [Field k] [IsAlgClosed k]
-- given
  (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
  (T : (Fin n → k) →ₗ[k] (Fin n → k))
  (h : ∀ W : Submodule k (Fin n → k),
    (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
  (hT : ∀ M ∈ A, ∀ v, T (M.mulVec v) = M.mulVec (T v)) :
-- imply
  ∃ c : k, ∀ v, T v = c • v := by
-- proof
  apply burnside_commutant A h T hT


/--
[burnside_dense](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/BurnsideMatrix.lean)
-/
@[main]
private lemma dense
  [Field k] [IsAlgClosed k]
-- given
  (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
  (h : ∀ W : Submodule k (Fin n → k),
    (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
  (m : ℕ) :
-- imply
  ∀ (x y : Fin m → (Fin n → k)),
    LinearIndependent k x → ∃ M ∈ A, ∀ i, M.mulVec (x i) = y i := by
-- proof
  apply burnside_dense A h m


/--
[burnside_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Algebra/BurnsideMatrix.lean)
-/
@[main]
private lemma burnside
  [Field k] [IsAlgClosed k]
-- given
  (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
  (h : ∀ W : Submodule k (Fin n → k),
    (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) :
-- imply
  A = ⊤ := by
-- proof
  apply burnside_matrix A h


-- created on 2026-10-09
