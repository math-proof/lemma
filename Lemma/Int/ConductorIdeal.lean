import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.ConductorIdeal
open Subalgebra


/--
[mem_conductorIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma mem_conductorIdeal_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S}
  {s : S} :
-- imply
  s ∈ A.conductorIdeal ↔ ∀ t : S, s * t ∈ A := by
-- proof
  apply Subalgebra.mem_conductorIdeal

/--
[le_conductorIdeal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma le_conductorIdeal_iff_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S}
  {I : Ideal S} :
-- imply
  I ≤ A.conductorIdeal ↔ (I : Set S) ⊆ (A : Set S) := by
-- proof
  apply Subalgebra.le_conductorIdeal_iff

/--
[conductorIdeal_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma conductorIdeal_subset_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S} :
-- imply
  (A.conductorIdeal : Set S) ⊆ (A : Set S) := by
-- proof
  apply Subalgebra.conductorIdeal_subset A

/--
[conductorIdeal_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma conductorIdeal_mono_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A B : Subalgebra R S}
-- given
  (h : A ≤ B) :
-- imply
  A.conductorIdeal ≤ B.conductorIdeal := by
-- proof
  apply Subalgebra.conductorIdeal_mono h

/--
[conductorIdeal_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma conductorIdeal_top_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S] :
-- imply
  (⊤ : Subalgebra R S).conductorIdeal = ⊤ := by
-- proof
  apply Subalgebra.conductorIdeal_top

/--
[conductorIdeal_eq_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma conductorIdeal_eq_top_iff_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S} :
-- imply
  A.conductorIdeal = ⊤ ↔ A = ⊤ := by
-- proof
  apply Subalgebra.conductorIdeal_eq_top_iff

/--
[conductorIdeal_comap_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma conductorIdeal_comap_le_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]
  {f : S →ₐ[R] T}
  {B : Subalgebra R T} :
-- imply
  (B.conductorIdeal).comap f.toRingHom ≤ (B.comap f).conductorIdeal := by
-- proof
  apply Subalgebra.conductorIdeal_comap_le f B

/--
[adjoin_conductorIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma adjoin_conductorIdeal_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T] [CommRing R'] [CommRing S'] [Algebra R' S']
  {x : S'} :
-- imply
  (Algebra.adjoin R' ({x} : Set S')).conductorIdeal = conductor R' x := by
-- proof
  apply Subalgebra.adjoin_conductorIdeal x

/--
[conductorIdeal_bot_ne_bot_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma conductorIdeal_bot_ne_bot_of_finite_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R]
  {T : Subalgebra R K} [Module.Finite R ↥T] :
-- imply
  (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ := by
-- proof
  apply Subalgebra.conductorIdeal_bot_ne_bot_of_finite T

/--
[finite_of_conductorIdeal_bot_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma finite_of_conductorIdeal_bot_ne_bot_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R] [IsNoetherianRing R]
  {T : Subalgebra R K}
-- given
  (h : (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥) :
-- imply
  Module.Finite R ↥T := by
-- proof
  apply Subalgebra.finite_of_conductorIdeal_bot_ne_bot T h

/--
[bot_conductorIdeal_ne_bot_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma bot_conductorIdeal_ne_bot_iff_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R] [IsNoetherianRing R]
  {T : Subalgebra R K} :
-- imply
  (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ ↔ Module.Finite R ↥T := by
-- proof
  apply Subalgebra.bot_conductorIdeal_ne_bot_iff T

/--
[integralClosure_bot_conductorIdeal_ne_bot_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
private lemma integralClosure_bot_conductorIdeal_ne_bot_iff_eq
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R] [IsNoetherianRing R]
  {T : Subalgebra R K} :
-- imply
  (⊥ : Subalgebra R ↥(integralClosure R K)).conductorIdeal ≠ ⊥ ↔
    Module.Finite R ↥(integralClosure R K) := by
-- proof
  apply Subalgebra.integralClosure_bot_conductorIdeal_ne_bot_iff T


-- created on 2026-10-20
