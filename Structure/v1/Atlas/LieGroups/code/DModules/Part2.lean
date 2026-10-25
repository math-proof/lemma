/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie
import Def.v1.Atlas.LieGroups.code.DModules.Part2
universe u v w


namespace DModules

open scoped TensorProduct

section DModulesSheaf

variable {k : Type u} [CommRing k]

structure LeftDModuleSheaf (k : Type u) [CommRing k] (D : SheafOfDiffOps.{u, v, w} k) where
  sections : D.I → Type w
  instAddCommGroup : ∀ i, AddCommGroup (sections i)
  instModule : ∀ i, @Module (D.diffOpsRing i) (sections i) (D.instDiffRing i).toSemiring
    (instAddCommGroup i).toAddCommMonoid
  restrict : ∀ {i j}, D.incl i j → sections i → sections j
  restrict_add : ∀ {i j} (h : D.incl i j) (s t : sections i),
    restrict h (letI := instAddCommGroup i; s + t) =
    letI := instAddCommGroup j; restrict h s + restrict h t
  restrict_smul : ∀ {i j} (h : D.incl i j) (d : D.diffOpsRing i) (s : sections i),
    restrict h (letI := instModule i; d • s) =
    letI := instModule j; D.diffOpsRestrict h d • restrict h s
  restrict_id : ∀ (i : D.I) (s : sections i), restrict (D.incl_refl i) s = s
  restrict_comp : ∀ {i j k : D.I} (hij : D.incl i j) (hjk : D.incl j k) (s : sections i),
    restrict (D.incl_trans hij hjk) s = restrict hjk (restrict hij s)
  locality : ∀ (i : D.I) (s : sections i),
    (∀ j, ∀ h : D.incl i j, restrict h s = letI := instAddCommGroup j; 0) →
    s = letI := instAddCommGroup i; 0
  gluing : ∀ {i : D.I} (cover : D.I → Prop)
    (hcover : ∀ j, cover j → D.incl i j)
    (sec : ∀ j, cover j → sections j),
    (∀ (j : D.I) (hj : cover j) (l : D.I) (hl : cover l)
      (m : D.I) (hjm : D.incl j m) (hlm : D.incl l m),
      restrict hjm (sec j hj) = restrict hlm (sec l hl)) →
    ∃ s : sections i, ∀ j (hj : cover j), restrict (hcover j hj) s = sec j hj
  quasicoherent : ∀ {i j} (h : D.incl i j) (s : sections j),
    ∃ (n : ℕ) (fs : Fin n → D.coordRing j) (gs : Fin n → sections i),
    s = letI := instAddCommGroup j
        letI := instModule j
        letI := D.instCommRing j
        letI := D.instDiffRing j
        letI := D.instDiffAlgebra j
        Finset.sum Finset.univ fun t =>
          (algebraMap (D.coordRing j) (D.diffOpsRing j) (fs t)) • restrict h (gs t)
  quasicoherent_iso : ∀ {i j} (h : D.incl i j),
    letI := D.baseChangeAddCommGroup h (sections i) (instAddCommGroup i) (instModule i)
    letI := instAddCommGroup j
    Nonempty ((D.baseChangeType h (sections i) (instAddCommGroup i) (instModule i)) ≃+ sections j)

structure RightDModuleSheaf (k : Type u) [CommRing k] (D : SheafOfDiffOps.{u, v, w} k) where
  sections : D.I → Type w
  instAddCommGroup : ∀ i, AddCommGroup (sections i)
  instModule : ∀ i, letI := D.instDiffRing i
    @Module (D.diffOpsRing i)ᵐᵒᵖ (sections i) (inferInstance : Semiring _)
      (instAddCommGroup i).toAddCommMonoid
  restrict : ∀ {i j}, D.incl i j → sections i → sections j
  restrict_add : ∀ {i j} (h : D.incl i j) (s t : sections i),
    restrict h (letI := instAddCommGroup i; s + t) =
    letI := instAddCommGroup j; restrict h s + restrict h t
  restrict_smul : ∀ {i j} (h : D.incl i j) (d : (D.diffOpsRing i)ᵐᵒᵖ) (s : sections i),
    restrict h (letI := D.instDiffRing i; letI := instModule i; d • s) =
    letI := D.instDiffRing j; letI := instModule j;
    MulOpposite.op (D.diffOpsRestrict h (MulOpposite.unop d)) • restrict h s
  restrict_id : ∀ (i : D.I) (s : sections i), restrict (D.incl_refl i) s = s
  restrict_comp : ∀ {i j k : D.I} (hij : D.incl i j) (hjk : D.incl j k) (s : sections i),
    restrict (D.incl_trans hij hjk) s = restrict hjk (restrict hij s)
  locality : ∀ (i : D.I) (s : sections i),
    (∀ j, ∀ h : D.incl i j, restrict h s = letI := instAddCommGroup j; 0) →
    s = letI := instAddCommGroup i; 0
  gluing : ∀ {i : D.I} (cover : D.I → Prop)
    (hcover : ∀ j, cover j → D.incl i j)
    (sec : ∀ j, cover j → sections j),
    (∀ (j : D.I) (hj : cover j) (l : D.I) (hl : cover l)
      (m : D.I) (hjm : D.incl j m) (hlm : D.incl l m),
      restrict hjm (sec j hj) = restrict hlm (sec l hl)) →
    ∃ s : sections i, ∀ j (hj : cover j), restrict (hcover j hj) s = sec j hj
  quasicoherent : ∀ {i j} (h : D.incl i j) (s : sections j),
    ∃ (n : ℕ) (fs : Fin n → D.coordRing j) (gs : Fin n → sections i),
    s = letI := instAddCommGroup j
        letI := D.instDiffRing j
        letI := instModule j
        letI := D.instCommRing j
        letI := D.instDiffAlgebra j
        Finset.sum Finset.univ fun t =>
          MulOpposite.op (algebraMap (D.coordRing j) (D.diffOpsRing j) (fs t)) • restrict h (gs t)

end DModulesSheaf

section Connections

structure Connection (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
    (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] where
  nabla : M →ₗ[k] (TensorProduct A M (KaehlerDifferential k A))
  leibniz : ∀ (f : A) (m : M), nabla (f • m) =
    f • nabla m + TensorProduct.mk A M (KaehlerDifferential k A) m (KaehlerDifferential.D k A f)

end Connections
end DModules
