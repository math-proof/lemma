import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.LindstromGesselViennot
open MetaMathlibExt


/--
[lindstrom_gessel_viennot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LindstromGesselViennot.lean)
-/
@[path]
private lemma lindstrom_gessel_viennot_eq
  [DecidableEq V] [CommRing R]
  {n : ℕ}
  {A B : Fin n → V}
  {rank : V → ℕ}
  {P : Fin n → Fin n → Finset (List V)}
  {e : Fin n → Fin n → R}
  {S : Finset (Fin n → List V)}
-- given
  (E : V → V → Prop)
  (hAcyc : ∀ u v : V, E u v → rank u < rank v)
  (hPath : ∀ i j : Fin n, ∀ p : List V, p ∈ P i j ↔ (p.head? = some (A i) ∧ p.getLast? = some (B j) ∧ p.IsChain (fun u v => E u v)))
  (he : ∀ i j : Fin n, e i j = ((P i j).card : R))
  (hPlanar : ∀ i j k l : Fin n, i < j → l < k → ∀ p ∈ P i k, ∀ q ∈ P j l, ∃ v : V, v ∈ p ∧ v ∈ q)
  (hSys : ∀ F : Fin n → List V, F ∈ S ↔ ((∀ i : Fin n, F i ∈ P i i) ∧ ∀ i j : Fin n, i ≠ j → Disjoint (F i).toFinset (F j).toFinset)) :
-- imply
  (S.card : R) = Matrix.det e := by
-- proof
  apply MetaMathlibExt.lindstrom_gessel_viennot n E A B rank hAcyc P hPath e he hPlanar S hSys


-- created on 2026-10-20
