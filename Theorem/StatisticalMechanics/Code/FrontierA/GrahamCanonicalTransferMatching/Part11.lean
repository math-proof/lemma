/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part11
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem symmDiffFold_pair
    {A : Type*} (s : Finset A) (f g : A -> Finset I) :
    symmDiffFold s (fun x => f x ∆ g x) =
      symmDiffFold s f ∆ symmDiffFold s g := by
  classical
  unfold symmDiffFold
  simpa using (Finset.fold_op_distrib (s := s)
    (op := fun X Y : Finset I => X ∆ Y) (f := f) (g := g)
    (b₁ := (∅ : Finset I)) (b₂ := (∅ : Finset I)))

theorem symmDiffFold_equiv
    {A : Type*} [Fintype A] (e : Equiv.Perm A) (f : A -> Finset I) :
    symmDiffFold Finset.univ (fun x => f (e x)) =
      symmDiffFold Finset.univ f := by
  classical
  unfold symmDiffFold
  calc
    _ = (Finset.univ.map e.toEmbedding).fold
        (fun X Y : Finset I => X ∆ Y) ∅ f := by
      rw [Finset.fold_map]
      rfl
    _ = _ := by simp


theorem symmDiffFold_const
    {A : Type*} (s : Finset A) (C : Finset I) :
    symmDiffFold s (fun _ => C) =
      if s.card % 2 = 0 then ∅ else C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symmDiffFold]
  | @insert a s ha ih =>
      simp only [symmDiffFold, Finset.fold_insert ha,
        Finset.card_insert_of_notMem ha]
      change C ∆ symmDiffFold s (fun _ => C) =
        if (s.card + 1) % 2 = 0 then ∅ else C
      rw [ih]
      have hmod : s.card % 2 = 0 ∨ s.card % 2 = 1 := by omega
      rcases hmod with hmod | hmod <;> simp [hmod, Nat.add_mod]


theorem sources_symmDiffFold
    {A : Type*} (ends : I -> Sym2 W) (s : Finset A)
    (f : A -> Finset I) :
    StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) =
      symmDiffFold s
        (fun a => StatMech.Sharpness.RandomCurrent.sources ends (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symmDiffFold, StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK]
  | @insert a s ha ih =>
      simp only [symmDiffFold, Finset.fold_insert ha]
      rw [StatMech.Sharpness.RandomCurrent.sources_symmDiff]
      change StatMech.Sharpness.RandomCurrent.sources ends (f a) ∆
          StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) =
        StatMech.Sharpness.RandomCurrent.sources ends (f a) ∆
          symmDiffFold s
            (fun a => StatMech.Sharpness.RandomCurrent.sources ends (f a))
      rw [ih]


theorem sources_symmDiffFold_of_constant
    {A : Type*} (ends : I -> Sym2 W) (s : Finset A)
    (f : A -> Finset I) (C : Finset W)
    (hsrc : ∀ a ∈ s,
      StatMech.Sharpness.RandomCurrent.sources ends (f a) = C) :
    StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) =
      if s.card % 2 = 0 then ∅ else C := by
  rw [sources_symmDiffFold]
  have hfold : symmDiffFold s
      (fun a => StatMech.Sharpness.RandomCurrent.sources ends (f a)) =
      symmDiffFold s (fun _ => C) := by
    unfold symmDiffFold
    apply Finset.fold_congr
    exact hsrc
  rw [hfold, symmDiffFold_const]


theorem sources_symmDiffFold_rightMaskRows
    {A : Type*} (ends : I -> Sym2 W) (m : Finset I)
    (j k l zero : W) (p : Finset I × Finset I)
    (s : Finset A) (Q : A -> rightMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.sources ends
        (symmDiffFold s (fun x => rowClass m (Q x).1.1 0)) =
      if s.card % 2 = 0 then ∅ else {j, k} ∆ {k, l} := by
  apply sources_symmDiffFold_of_constant
  intro x _
  exact (rightPattern_rowBoundaries (Q x).1.2).1


theorem symmDiffFold_endpointCancellation
    {A : Type*} [Fintype A]
    (Q R : A -> Finset I) (σ : Equiv.Perm A) :
    symmDiffFold Finset.univ
        (fun x => Q x ∆ R x ∆ R (σ x)) =
      symmDiffFold Finset.univ Q := by
  rw [symmDiffFold_pair, symmDiffFold_pair,
    symmDiffFold_equiv σ R]
  simp

theorem symmDiff_left_cancel_finset
    (X A B : Finset I) (h : X ∆ A = X ∆ B) : A = B := by
  have h' := congrArg (fun K : Finset I => X ∆ K) h
  simpa [symmDiff_assoc] using h'


theorem exists_referenceTransferFold_eq_of_translatedRowPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S)
    (hrows : ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p,
      RowSupportDisconnects ends m
          (canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1) k zero ∧
        canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
          canonicalTranslatedRow ends m k zero b.1.1 (σ x).1.1.1) :
    ∃ a b : ↑S -> leftMaskFiber ends m j k l zero p,
      (∀ x, RowSupportDisconnects ends m
        (canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1)
          k zero) ∧
      (∀ x, canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero
          (b x).1.1 (σ x).1.1.1) ∧
      symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (a x).1.1) =
        symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (b x).1.1) := by
  classical
  choose a b hdisc heq using hrows
  refine ⟨a, b, hdisc, heq, ?_⟩
  let R := fun x : ↑S => rowClass m x.1.1.1 0
  let A := fun x : ↑S =>
    canonicalTransferUnion ends m k zero (a x).1.1
  let B := fun x : ↑S =>
    canonicalTransferUnion ends m k zero (b x).1.1
  have hpoint : ∀ x, R x ∆ A x = R (σ x) ∆ B x := by
    intro x
    simpa only [R, A, B, canonicalTranslatedRow] using heq x
  have hfold : symmDiffFold Finset.univ (fun x => R x ∆ A x) =
      symmDiffFold Finset.univ (fun x => R (σ x) ∆ B x) := by
    unfold symmDiffFold
    apply Finset.fold_congr
    intro x _
    exact hpoint x
  rw [symmDiffFold_pair, symmDiffFold_pair,
    symmDiffFold_equiv σ R] at hfold
  exact symmDiff_left_cancel_finset _ _ _ hfold


theorem canonicalTranslatedRow_opposite_eq_of_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero a x =
      canonicalTranslatedRow ends m k zero b y) :
    canonicalTranslatedRow ends m k zero b x =
      canonicalTranslatedRow ends m k zero a y := by
  unfold canonicalTranslatedRow at hxy ⊢
  let Ra := rowClass m x 0
  let Ry := rowClass m y 0
  let Ta := canonicalTransferUnion ends m k zero a
  let Tb := canonicalTransferUnion ends m k zero b
  change Ra ∆ Ta = Ry ∆ Tb at hxy
  change Ra ∆ Tb = Ry ∆ Ta
  calc
    Ra ∆ Tb = (Ra ∆ Ta) ∆ Ta ∆ Tb := by simp
    _ = (Ry ∆ Tb) ∆ Ta ∆ Tb := by rw [hxy]
    _ = Ry ∆ Ta := by
      calc
        (Ry ∆ Tb) ∆ Ta ∆ Tb =
            Ry ∆ Ta ∆ (Tb ∆ Tb) := by ac_rfl
        _ = Ry ∆ Ta := by simp


theorem canonicalTranslatedRow_opposite_rootCutBranches_iff_of_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero a x =
      canonicalTranslatedRow ends m k zero b y) :
    let Kx := canonicalTranslatedRow ends m k zero b x
    let Ky := canonicalTranslatedRow ends m k zero a y
    ((StatMech.Sharpness.RandomCurrent.connK ends Kx k zero ∧
          edgeComponent ends Kx zero = edgeComponent ends Kx k) ↔
        (StatMech.Sharpness.RandomCurrent.connK ends Ky k zero ∧
          edgeComponent ends Ky zero = edgeComponent ends Ky k)) ∧
      ((StatMech.Sharpness.RandomCurrent.connK ends (m \ Kx) k zero ∧
          edgeComponent ends (m \ Kx) zero =
            edgeComponent ends (m \ Kx) k) ↔
        (StatMech.Sharpness.RandomCurrent.connK ends (m \ Ky) k zero ∧
          edgeComponent ends (m \ Ky) zero =
            edgeComponent ends (m \ Ky) k)) := by
  dsimp only
  rw [canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a b x y hxy]
  exact ⟨Iff.rfl, Iff.rfl⟩


theorem canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b x y : leftMaskFiber ends m j k l zero p)
    (hxy : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 y.1.1) :
    CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ↔
      CanonicalTransferWorks ends m k zero a.1.1 y.1.1 := by
  rw [canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl b x,
    canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl a y,
    canonicalTranslatedRow_opposite_eq_of_eq
      ends m k zero a.1.1 b.1.1 x.1.1 y.1.1 hxy]


theorem exists_two_common_canonicalMaskRightImages_of_collisionSquare
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b x y : leftMaskFiber ends m j k l zero p)
    (hxyne : x ≠ y)
    (hax : CanonicalTransferWorks ends m k zero a.1.1 x.1.1)
    (hxy : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 y.1.1)
    (hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1) :
    ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
      q₁ ≠ q₂ ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p y := by
  have hdisc := (canonicalTransferWorks_iff_translatedRowDisconnects
    hloop hjk hkl a x).mp hax
  have hby : CanonicalTransferWorks ends m k zero b.1.1 y.1.1 :=
    (canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl b y).mpr (hxy ▸ hdisc)
  have hopp := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a.1.1 b.1.1 x.1.1 y.1.1 hxy
  have hay : CanonicalTransferWorks ends m k zero a.1.1 y.1.1 :=
    (canonicalTransferWorks_opposite_iff_of_translatedRow_eq
      hloop hjk hkl a b x y hxy).mp hbx
  let q₁ := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p a x hax
  let q₂ := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p b x hbx
  have hq₁x : q₁ ∈ canonicalMaskRightImages
      ends m j k l zero p x :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p x q₁).mpr ⟨a, hax, rfl⟩
  have hraw₁ := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl a b x y).mpr hxy
  have hq₁y : q₁ ∈ canonicalMaskRightImages
      ends m j k l zero p y :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p y q₁).mpr ⟨b, hby, hraw₁⟩
  have hq₂x : q₂ ∈ canonicalMaskRightImages
      ends m j k l zero p x :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p x q₂).mpr ⟨b, hbx, rfl⟩
  have hraw₂ := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl b a x y).mpr hopp
  have hq₂y : q₂ ∈ canonicalMaskRightImages
      ends m j k l zero p y :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p y q₂).mpr ⟨a, hay, hraw₂⟩
  have hTne : canonicalTransferUnion ends m k zero a.1.1 ≠
      canonicalTransferUnion ends m k zero b.1.1 := by
    intro hT
    have hrow : rowClass m x.1.1 0 = rowClass m y.1.1 0 :=
      symmDiff_left_cancel_finset
        (canonicalTransferUnion ends m k zero a.1.1) _ _ (by
          simpa only [canonicalTranslatedRow, hT, symmDiff_comm] using hxy)
    exact hxyne (leftMaskFiber_rowClass_zero_injective
      ends m j k l zero p hrow)
  refine ⟨q₁, q₂, ?_, hq₁x, hq₁y, hq₂x, hq₂y⟩
  intro hq
  have hrowq := congrArg
    (fun q : rightMaskFiber ends m j k l zero p => rowClass m q.1.1 0) hq
  dsimp only [q₁, q₂] at hrowq
  rw [rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a x hax,
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p b x hbx] at hrowq
  apply hTne
  exact symmDiff_left_cancel_finset (rowClass m x.1.1 0) _ _ hrowq


end StatMech.GrahamGHS.FourColor
