/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CoveringSystem/ExactCover.lean -/

import sympy.atlas.NumberTheory.CoveringSystem
import Lemma.Int.CoveringSystem
namespace Int

/-!
# Exact covers by residue classes

Source: Y. Movshovich, *Raabe's Identity and Covering Systems*, Journal of Integer Sequences
23 (2020),
[`movsho5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL23/Movshovich/movsho5.tex).

The definitions extend the repository's indexed covering-system API. In particular, coverage
multiplicity is counted by indices, rather than after converting the family to a `Finset` and
thereby losing repeated residue classes.
-/

/-- Number of indexed residue classes containing `z`. -/
def indexedCoverMultiplicity {k : ℕ} (moduli : Fin k → ℕ)
    (residues : Fin k → ℤ) (z : ℤ) : ℕ :=
  (Finset.univ.filter fun i => z ≡ residues i [ZMOD (moduli i : ℤ)]).card

/-- An indexed system is an exact `M`-cover of `target` when each point of `target` lies in
exactly `M` indexed classes and each point outside `target` lies in none. The source's systems
have at least two classes and positive moduli. -/
def IsExactCoverOf {k : ℕ} (moduli : Fin k → ℕ) (residues : Fin k → ℤ)
    (M : ℕ) (target : Set ℤ) : Prop :=
  2 ≤ k ∧ (∀ i, 0 < moduli i) ∧
    (∀ z, z ∈ target → indexedCoverMultiplicity moduli residues z = M) ∧
    ∀ z, z ∉ target → indexedCoverMultiplicity moduli residues z = 0

end Int
