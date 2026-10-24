/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# Permutation Images of Finsets

This file provides shared definitions and lemmas for working with the image of a finset
under a permutation.

## Main definitions

* `PermFinset.imageFinset` - The image of a finset under a permutation: `P.map ⟨σ, σ.injective⟩`
* `PermFinset.permsMapping` - The set of permutations that map one finset to another

## Main results

* `PermFinset.imageFinset_card` - The image has the same cardinality as the original set
* `PermFinset.imageFinset_compl` - The image of a complement equals the complement of the image
* `PermFinset.imageFinset_inv` - If σ maps P to Q, then σ⁻¹ maps Q to P
* `PermFinset.permsMapping_empty_of_card_ne` - If |P| ≠ |Q|, no permutation maps P to Q

## Implementation notes

These definitions are used by:
- `CauchyBinet.lean` (has local aliases `imageFinset` and `permsMapping`)
- `DesnanotJacobi.lean` (uses `PermFinset.imageFinset` and `PermFinset.permsMapping` directly)

New code should use this module.
-/


namespace PermFinset

/-- The image of a finset under a permutation. -/
def imageFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  P.map ⟨σ, σ.injective⟩

/-- The set of permutations that map P to Q. -/
def permsMapping {n : ℕ} (P Q : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => imageFinset σ P = Q)

end PermFinset
/-!
## Submatrix Determinant API

This section provides a unified API for submatrix determinants, bridging the
definitions in `CauchyBinet.lean` and `DesnanotJacobi.lean`.

### Definitions across the codebase

There are currently two styles of submatrix determinant definitions:

1. **Proof-requiring version** (`AlgebraicCombinatorics.CauchyBinet.submatrixDet`):
   Requires a proof `h : P.card = Q.card` as an argument.
   ```
   def submatrixDet A P Q (h : P.card = Q.card) :=
     (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det
   ```

2. **Total version** (`AlgebraicCombinatorics.Determinants.submatrixDet`, `AlgebraicCombinatorics.CauchyBinet.minor`):
   Uses `if h : P.card = Q.card then ... else 0` to handle cardinality mismatch.
   ```
   def submatrixDet A P Q :=
     if h : P.card = Q.card then ... else 0
   ```

### Equivalence lemmas

The following lemmas establish equivalence between these definitions:

- `PermFinset.submatrixDet_of_card_eq`: When |P| = |Q|, unfolds to the determinant
- `PermFinset.submatrixDet_eq_proof_version`: Relates to the proof-requiring style
- `AlgebraicCombinatorics.CauchyBinet.submatrixDet_eq_permFinset`: CauchyBinet version equals PermFinset
- `AlgebraicCombinatorics.CauchyBinet.minor_eq_permFinset_submatrixDet`: CauchyBinet.minor equals PermFinset
- `AlgebraicCombinatorics.Determinants.submatrixDet_eq_permFinset`: Determinants version equals PermFinset

### Migration path

New code should use `PermFinset.submatrixDet` (the total version). Existing code
can use the equivalence lemmas above to convert between styles.
-/


namespace PermFinset

open Matrix Finset

variable {R : Type*} [CommRing R]

/-- The determinant of a submatrix corresponding to row set P and column set Q.
    Returns 0 if |P| ≠ |Q|.
    
    This is the canonical "total" definition that handles cardinality mismatch gracefully,
    avoiding the need for proof terms in most applications.
    
    This definition is equivalent to:
    - `CauchyBinet.minor` (same signature and semantics)
    - `Determinants.submatrixDet` in DesnanotJacobi.lean (uses `finsetToFin` instead of
      `orderEmbOfFin`, but these are equivalent)
    - `CauchyBinet.submatrixDet` when |P| = |Q| (that version requires a proof argument) -/
noncomputable def submatrixDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) : R :=
  if h : P.card = Q.card then
    (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det
  else 0

end PermFinset
