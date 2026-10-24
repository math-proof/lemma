/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Basic.Countable.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

section
/-!
# Higman–Neumann–Neumann embedding theorem

Records that every countable group embeds into a two-generator group.
-/

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

universe u

open SemidirectProduct
private noncomputable def shiftAut : MulAut (FreeGroup ℤ) :=
  FreeGroup.freeGroupCongr (Equiv.addRight (1 : ℤ))
private noncomputable def shiftHom : Multiplicative ℤ →* MulAut (FreeGroup ℤ) :=
  (zpowersHom (MulAut (FreeGroup ℤ))) shiftAut
private abbrev K (G : Type*) [Group G] := Monoid.Coprod G (FreeGroup (Fin 2))
private noncomputable def aK (G : Type*) [Group G] : K G :=
  Monoid.Coprod.inr (FreeGroup.of (0 : Fin 2))
private noncomputable def bK (G : Type*) [Group G] : K G :=
  Monoid.Coprod.inr (FreeGroup.of (1 : Fin 2))
private noncomputable def alpha (G : Type*) [Group G] : FreeGroup ℕ →* K G :=
  FreeGroup.lift (fun i : ℕ => (bK G ^ (-(i : ℤ))) * aK G * (bK G ^ ((i : ℤ))))
private noncomputable def psiA : FreeGroup (Fin 2) →* (FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) :=
  FreeGroup.lift (fun i : Fin 2 => if i = (0 : Fin 2) then inl (FreeGroup.of (0:ℤ)) else inr
      (Multiplicative.ofAdd (1:ℤ)))

private noncomputable def beta (G : Type*) [Group G] (g : ℕ → G) : FreeGroup ℕ →* K G :=
  FreeGroup.lift (fun i : ℕ => Monoid.Coprod.inl (g i) *
      ((aK G ^ (-(i : ℤ))) * bK G * (aK G ^ ((i : ℤ)))))

private noncomputable def psiB : FreeGroup (Fin 2) →* (FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) :=
  FreeGroup.lift (fun i : Fin 2 => if i = (0 : Fin 2) then inr (Multiplicative.ofAdd (1:ℤ)) else inl
      (FreeGroup.of (0:ℤ)))
end MathlibExt.GroupTheory.HNNEmbeddingWanted
end
