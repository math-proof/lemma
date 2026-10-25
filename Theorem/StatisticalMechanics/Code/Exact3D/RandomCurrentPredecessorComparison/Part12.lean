/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part11
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

@[simp] theorem edgeCopySourcePairData_swap_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (d : edgeCopySourcePairData G A B) :
    (edgeCopySourcePairData_swap G d).1 = d.1 := by
  rcases d with ⟨m, K, hK⟩
  rfl

@[simp] theorem edgeCopySourcePairDataWeight_swap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {A B : Finset V} (d : edgeCopySourcePairData G A B) :
    edgeCopySourcePairDataWeight G β J (edgeCopySourcePairData_swap G d) =
      edgeCopySourcePairDataWeight G β J d := by
  rcases d with ⟨m, K, hK⟩
  rfl

@[simp] theorem edgeCopySourcePairData_swap_swap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (d : edgeCopySourcePairData G A B) :
    edgeCopySourcePairData_swap G (edgeCopySourcePairData_swap G d) = d := by
  rcases d with ⟨m, K, hK⟩
  dsimp [edgeCopySourcePairData_swap]
  simp

theorem edgeCopySourcePairData_swap_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} :
    Function.Injective
      (edgeCopySourcePairData_swap (G := G) (A := A) (B := B)) := by
  intro d e h
  have hswap :=
    congrArg
      (edgeCopySourcePairData_swap (G := G) (A := B) (B := A)) h
  simpa using hswap

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {α : Type*} {s : Finset α}
    {profileRoute : α → ↥G.edgeFinset → ℕ}
    (witness :
      (a : α) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a)))
    (hwitness :
      ∀ a,
        witness a ∈ edgeCopySourcePairWitnesses G A B (profileRoute a))
    (hinj : Set.InjOn profileRoute s) :
    Set.InjOn
      (fun a => edgeCopySourcePairData_of_witness G (hwitness a)) s := by
  intro a ha b hb hdata
  exact hinj ha hb (by
    simpa using congrArg Sigma.fst hdata)

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_attach_routes_of_profileWitness_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    {α : Type*} (s : Finset α) (F : α → ℝ)
    (profileRoute : {a : α // a ∈ s} → ↥G.edgeFinset → ℕ)
    (witness :
      (a : {a : α // a ∈ s}) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a)))
    (hwitness :
      ∀ a,
        witness a ∈ edgeCopySourcePairWitnesses G A B (profileRoute a))
    (hinj : Function.Injective profileRoute)
    (hpoint :
      ∀ a : {a : α // a ∈ s},
        F a.1 ≤
          c * Sharpness.weight G β J
            (Sharpness.ofEdgeFun G (profileRoute a))) :
    ∃ route : {a : α // a ∈ s} → edgeCopySourcePairData G A B,
      Function.Injective route ∧
        ∀ a : α,
          ∀ ha : a ∈ s,
            F a ≤ c * edgeCopySourcePairDataWeight G β J (route ⟨a, ha⟩) := by
  classical
  let route : {a : α // a ∈ s} → edgeCopySourcePairData G A B :=
    fun a => edgeCopySourcePairData_of_witness G (hwitness a)
  refine ⟨route, ?_, ?_⟩
  · intro a b hdata
    exact hinj (by
      simpa [route] using congrArg Sigma.fst hdata)
  · intro a ha
    simpa [route] using hpoint ⟨a, ha⟩

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_attach_routes_of_sourceEquation_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    {α : Type*} (s : Finset α) (F : α → ℝ)
    (profileRoute : {a : α // a ∈ s} → ↥G.edgeFinset → ℕ)
    (witness :
      (a : {a : α // a ∈ s}) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a)))
    (hleft :
      ∀ a,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute a)) (witness a) =
          A)
    (hright :
      ∀ a,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute a))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a))) \
            witness a) =
          B)
    (hinj : Function.Injective profileRoute)
    (hpoint :
      ∀ a : {a : α // a ∈ s},
        F a.1 ≤
          c * Sharpness.weight G β J
            (Sharpness.ofEdgeFun G (profileRoute a))) :
    ∃ route : {a : α // a ∈ s} → edgeCopySourcePairData G A B,
      Function.Injective route ∧
        ∀ a : α,
          ∀ ha : a ∈ s,
            F a ≤ c * edgeCopySourcePairDataWeight G β J (route ⟨a, ha⟩) := by
  refine
    edgeCopySourcePairData_attach_routes_of_profileWitness_routes
      G β J c s F profileRoute witness ?_ hinj hpoint
  intro a
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft a, hright a⟩

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_attach_splitRoutes_of_profileWitness_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    {α Split : Type*} (s : Finset α) (F : α → ℝ)
    (split : {a : α // a ∈ s} → Finset Split)
    (profileRoute :
      (a : {a : α // a ∈ s}) → Split → ↥G.edgeFinset → ℕ)
    (witness :
      (a : {a : α // a ∈ s}) → (i : Split) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a i)))
    (hwitness :
      ∀ a i,
        witness a i ∈ edgeCopySourcePairWitnesses G A B
          (profileRoute a i))
    (hinj :
      Set.InjOn
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          profileRoute p.1 p.2)
        (s.attach.sigma split))
    (hpoint :
      ∀ a : {a : α // a ∈ s},
        F a.1 ≤
          ∑ i ∈ split a,
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute a i))) :
    ∃ route :
        (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B,
      Set.InjOn
          (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
            route p.1 p.2)
          (s.attach.sigma split) ∧
        ∀ a : α,
          ∀ ha : a ∈ s,
            F a ≤
              ∑ i ∈ split ⟨a, ha⟩,
                c * edgeCopySourcePairDataWeight G β J
                  (route ⟨a, ha⟩ i) := by
  classical
  let route :
      (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B :=
    fun a i => edgeCopySourcePairData_of_witness G (hwitness a i)
  refine ⟨route, ?_, ?_⟩
  · simpa [route] using
      edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
        G (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          witness p.1 p.2)
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          hwitness p.1 p.2)
        hinj
  · intro a ha
    simpa [route] using hpoint ⟨a, ha⟩

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_attach_splitRoutes_of_sourceEquation_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    {α Split : Type*} (s : Finset α) (F : α → ℝ)
    (split : {a : α // a ∈ s} → Finset Split)
    (profileRoute :
      (a : {a : α // a ∈ s}) → Split → ↥G.edgeFinset → ℕ)
    (witness :
      (a : {a : α // a ∈ s}) → (i : Split) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a i)))
    (hleft :
      ∀ a i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute a i))
          (witness a i) =
          A)
    (hright :
      ∀ a i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute a i))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a i))) \
            witness a i) =
          B)
    (hinj :
      Set.InjOn
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          profileRoute p.1 p.2)
        (s.attach.sigma split))
    (hpoint :
      ∀ a : {a : α // a ∈ s},
        F a.1 ≤
          ∑ i ∈ split a,
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute a i))) :
    ∃ route :
        (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B,
      Set.InjOn
          (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
            route p.1 p.2)
          (s.attach.sigma split) ∧
        ∀ a : α,
          ∀ ha : a ∈ s,
            F a ≤
              ∑ i ∈ split ⟨a, ha⟩,
                c * edgeCopySourcePairDataWeight G β J
                  (route ⟨a, ha⟩ i) := by
  refine
    edgeCopySourcePairData_attach_splitRoutes_of_profileWitness_routes
      G β J c s F split profileRoute witness ?_ hinj hpoint
  intro a i
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft a i, hright a i⟩

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairData_attach_splitRoutes_of_sourceEquation_routes_beta_div_six_div_384
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ)
    {α Split : Type*} (s : Finset α) (F : α → ℝ)
    (split : {a : α // a ∈ s} → Finset Split)
    (profileRoute :
      (a : {a : α // a ∈ s}) → Split → ↥G.edgeFinset → ℕ)
    (witness :
      (a : {a : α // a ∈ s}) → (i : Split) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a i)))
    (hleft :
      ∀ a i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute a i))
          (witness a i) =
          A)
    (hright :
      ∀ a i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute a i))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a i))) \
            witness a i) =
          B)
    (hinj :
      Set.InjOn
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          profileRoute p.1 p.2)
        (s.attach.sigma split))
    (hpoint :
      ∀ a : {a : α // a ∈ s},
        F a.1 ≤
          ∑ i ∈ split a,
            ((β / 6) *
              Sharpness.weight G β J
                (Sharpness.ofEdgeFun G (profileRoute a i))) /
              384) :
    ∃ route :
        (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B,
      Set.InjOn
          (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
            route p.1 p.2)
          (s.attach.sigma split) ∧
        ∀ a : α,
          ∀ ha : a ∈ s,
            F a ≤
              ∑ i ∈ split ⟨a, ha⟩,
                ((β / 6) *
                  edgeCopySourcePairDataWeight G β J
                    (route ⟨a, ha⟩ i)) /
                  384 := by
  classical
  have hwitness :
      ∀ a i,
        witness a i ∈ edgeCopySourcePairWitnesses G A B
          (profileRoute a i) := by
    intro a i
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft a i, hright a i⟩
  let route :
      (a : {a : α // a ∈ s}) → Split → edgeCopySourcePairData G A B :=
    fun a i => edgeCopySourcePairData_of_witness G (hwitness a i)
  refine ⟨route, ?_, ?_⟩
  · simpa [route] using
      edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
        G (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          witness p.1 p.2)
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          hwitness p.1 p.2)
        hinj
  · intro a ha
    simpa [route] using hpoint ⟨a, ha⟩

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_twoRow_splitRoutes_of_sourceEquation_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ)
    {Split : Type*}
    (split0 split1 : Finset Split)
    (F0 F1 : ℝ)
    (profileRoute0 profileRoute1 : Split → ↥G.edgeFinset → ℕ)
    (witness0 :
      (i : Split) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute0 i)))
    (witness1 :
      (i : Split) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute1 i)))
    (hleft0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute0 i))
          (witness0 i) =
          A)
    (hright0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute0 i))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute0 i))) \
            witness0 i) =
          B)
    (hleft1 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute1 i))
          (witness1 i) =
          A)
    (hright1 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute1 i))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute1 i))) \
            witness1 i) =
          B)
    (hinj0 : Set.InjOn profileRoute0 split0)
    (hinj1 : Set.InjOn profileRoute1 split1)
    (hdisj :
      ∀ i ∈ split0, ∀ j ∈ split1, profileRoute0 i ≠ profileRoute1 j)
    (hpoint0 :
      F0 ≤
        ∑ i ∈ split0,
          ((β / 6) *
            Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute0 i))) /
            384)
    (hpoint1 :
      F1 ≤
        ∑ i ∈ split1,
          ((β / 6) *
            Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute1 i))) /
            384) :
    ∃ route0 route1 : Split → edgeCopySourcePairData G A B,
      Set.InjOn route0 split0 ∧
        Set.InjOn route1 split1 ∧
          (∀ i ∈ split0, ∀ j ∈ split1, route0 i ≠ route1 j) ∧
            (F0 ≤
              ∑ i ∈ split0,
                ((β / 6) *
                  edgeCopySourcePairDataWeight G β J (route0 i)) /
                  384) ∧
              (F1 ≤
                ∑ i ∈ split1,
                  ((β / 6) *
                    edgeCopySourcePairDataWeight G β J (route1 i)) /
                    384) := by
  classical
  have hwitness0 :
      ∀ i,
        witness0 i ∈ edgeCopySourcePairWitnesses G A B
          (profileRoute0 i) := by
    intro i
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft0 i, hright0 i⟩
  have hwitness1 :
      ∀ i,
        witness1 i ∈ edgeCopySourcePairWitnesses G A B
          (profileRoute1 i) := by
    intro i
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft1 i, hright1 i⟩
  let route0 : Split → edgeCopySourcePairData G A B :=
    fun i => edgeCopySourcePairData_of_witness G (hwitness0 i)
  let route1 : Split → edgeCopySourcePairData G A B :=
    fun i => edgeCopySourcePairData_of_witness G (hwitness1 i)
  refine ⟨route0, route1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [route0] using
      edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
        (G := G) (s := split0) witness0 hwitness0 hinj0
  · simpa [route1] using
      edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
        (G := G) (s := split1) witness1 hwitness1 hinj1
  · intro i hi j hj hroute
    exact hdisj i hi j hj (by
      simpa [route0, route1] using congrArg Sigma.fst hroute)
  · simpa [route0] using hpoint0
  · simpa [route1] using hpoint1

set_option linter.style.longLine false in


theorem finset_attach_sigma_singleton_route_injective_of_injOn
    {α Split Target : Type*} {s : Finset α}
    {split : {a : α // a ∈ s} → Finset Split}
    {label : {a : α // a ∈ s} → Split}
    {route : {a : α // a ∈ s} → Split → Target}
    (hinj :
      Set.InjOn
        (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) =>
          route p.1 p.2)
        (s.attach.sigma split))
    (hsplit : ∀ a : {a : α // a ∈ s}, split a = {label a}) :
    Function.Injective (fun a : {a : α // a ∈ s} => route a (label a)) := by
  intro a b hroute
  apply Subtype.ext
  have ha :
      (Sigma.mk a (label a) :
          Sigma (fun _ : {a : α // a ∈ s} => Split)) ∈
        s.attach.sigma split := by
    rw [Finset.mem_sigma]
    exact ⟨by simp, by simp [hsplit a]⟩
  have hb :
      (Sigma.mk b (label b) :
          Sigma (fun _ : {a : α // a ∈ s} => Split)) ∈
        s.attach.sigma split := by
    rw [Finset.mem_sigma]
    exact ⟨by simp, by simp [hsplit b]⟩
  have hp :
      (Sigma.mk a (label a) :
          Sigma (fun _ : {a : α // a ∈ s} => Split)) =
        Sigma.mk b (label b) :=
    hinj ha hb hroute
  exact congrArg
    (fun p : Sigma (fun _ : {a : α // a ∈ s} => Split) => p.1.1) hp

set_option linter.style.longLine false in


theorem edgeCopySourcePair_sourceEquationSubroute_of_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    {α : Type*} (s : Finset α) (F : α → ℝ)
    (hempty : s = ∅) :
    ∃ profileRoute : {a : α // a ∈ s} → ↥G.edgeFinset → ℕ,
      ∃ witness :
          (a : {a : α // a ∈ s}) →
            Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a)),
        (∀ a,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G (profileRoute a)) (witness a) =
            A) ∧
          (∀ a,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G (profileRoute a))
              ((Finset.univ :
                  Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a))) \
                witness a) =
              B) ∧
            Function.Injective profileRoute ∧
              ∀ a : α,
                ∀ ha : a ∈ s,
                  F a ≤ c * Sharpness.weight G β J
                    (Sharpness.ofEdgeFun G (profileRoute ⟨a, ha⟩)) := by
  classical
  have hfalse : ∀ a : {a : α // a ∈ s}, False := by
    intro a
    have hmem : a.1 ∈ (∅ : Finset α) := by
      simpa [hempty] using a.2
    simp at hmem
  let profileRoute : {a : α // a ∈ s} → ↥G.edgeFinset → ℕ :=
    fun a => False.elim (hfalse a)
  let witness :
      (a : {a : α // a ∈ s}) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute a)) :=
    fun a => False.elim (hfalse a)
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a
    exact False.elim (hfalse a)
  · intro a
    exact False.elim (hfalse a)
  · intro a _b _h
    exact False.elim (hfalse a)
  · intro a ha
    simp [hempty] at ha

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_supportPattern_routes_of_profileWitness_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    (Ωactive : Finset (↥G.edgeFinset → ℕ))
    (supportPatterns : Finset (Finset ↥G.edgeFinset))
    (supportOf : (↥G.edgeFinset → ℕ) → Finset ↥G.edgeFinset)
    (F : (↥G.edgeFinset → ℕ) → ℝ)
    (profileRoute :
      Finset ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        (↥G.edgeFinset → ℕ))
    (witness :
      (S : Finset ↥G.edgeFinset) → (m : ↥G.edgeFinset → ℕ) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute S m)))
    (hwitness :
      ∀ S m,
        witness S m ∈ edgeCopySourcePairWitnesses G A B (profileRoute S m))
    (hinj :
      ∀ S ∈ supportPatterns,
        Set.InjOn (profileRoute S)
          (Ωactive.filter (fun m => supportOf m = S)))
    (hsupport :
      ∀ S ∈ supportPatterns,
        ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
          supportOf (profileRoute S m) = S)
    (hpoint :
      ∀ S ∈ supportPatterns,
        ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
          F m ≤
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute S m))) :
    ∃ route :
        Finset ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
          edgeCopySourcePairData G A B,
      (∀ S ∈ supportPatterns,
        Set.InjOn (route S)
          (Ωactive.filter (fun m => supportOf m = S))) ∧
        (∀ S ∈ supportPatterns,
          ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
            supportOf (route S m).1 = S) ∧
          ∀ S ∈ supportPatterns,
            ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
              F m ≤ c * edgeCopySourcePairDataWeight G β J (route S m) := by
  classical
  let route :
      Finset ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        edgeCopySourcePairData G A B :=
    fun S m => edgeCopySourcePairData_of_witness G (hwitness S m)
  refine ⟨route, ?_, ?_, ?_⟩
  · intro S hS
    exact
      edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
        G (fun m => witness S m) (fun m => hwitness S m) (hinj S hS)
  · intro S hS m hm
    simpa [route] using hsupport S hS m hm
  · intro S hS m hm
    simpa [route] using hpoint S hS m hm

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_supportPattern_routes_of_sourceEquation_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    (Ωactive : Finset (↥G.edgeFinset → ℕ))
    (supportPatterns : Finset (Finset ↥G.edgeFinset))
    (supportOf : (↥G.edgeFinset → ℕ) → Finset ↥G.edgeFinset)
    (F : (↥G.edgeFinset → ℕ) → ℝ)
    (profileRoute :
      Finset ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        (↥G.edgeFinset → ℕ))
    (witness :
      (S : Finset ↥G.edgeFinset) → (m : ↥G.edgeFinset → ℕ) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute S m)))
    (hleft :
      ∀ S m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute S m))
          (witness S m) =
          A)
    (hright :
      ∀ S m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute S m))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute S m))) \
            witness S m) =
          B)
    (hinj :
      ∀ S ∈ supportPatterns,
        Set.InjOn (profileRoute S)
          (Ωactive.filter (fun m => supportOf m = S)))
    (hsupport :
      ∀ S ∈ supportPatterns,
        ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
          supportOf (profileRoute S m) = S)
    (hpoint :
      ∀ S ∈ supportPatterns,
        ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
          F m ≤
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute S m))) :
    ∃ route :
        Finset ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
          edgeCopySourcePairData G A B,
      (∀ S ∈ supportPatterns,
        Set.InjOn (route S)
          (Ωactive.filter (fun m => supportOf m = S))) ∧
        (∀ S ∈ supportPatterns,
          ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
            supportOf (route S m).1 = S) ∧
          ∀ S ∈ supportPatterns,
            ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
              F m ≤ c * edgeCopySourcePairDataWeight G β J (route S m) := by
  refine
    edgeCopySourcePairData_supportPattern_routes_of_profileWitness_routes
      G β J c Ωactive supportPatterns supportOf F profileRoute witness ?_
      hinj hsupport hpoint
  intro S m
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft S m, hright S m⟩

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_ownerIndexed_routes_of_profileWitness_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    (Ωactive : Finset (↥G.edgeFinset → ℕ))
    (owners : Finset ↥G.edgeFinset)
    (rowPred : ↥G.edgeFinset → (↥G.edgeFinset → ℕ) → Prop)
    [∀ ew, DecidablePred (rowPred ew)]
    (supportOf : (↥G.edgeFinset → ℕ) → Finset ↥G.edgeFinset)
    (F : (↥G.edgeFinset → ℕ) → ℝ)
    (profileRoute :
      ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        (↥G.edgeFinset → ℕ))
    (witness :
      (ew : ↥G.edgeFinset) → (m : ↥G.edgeFinset → ℕ) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute ew m)))
    (hwitness :
      ∀ ew m,
        witness ew m ∈ edgeCopySourcePairWitnesses G A B
          (profileRoute ew m))
    (hinj :
      ∀ ew ∈ owners,
        Set.InjOn (profileRoute ew) (Ωactive.filter (rowPred ew)))
    (hsupport :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (rowPred ew),
          supportOf (profileRoute ew m) = {ew})
    (hpoint :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (rowPred ew),
          F m ≤
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute ew m))) :
    ∃ route :
        ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
          edgeCopySourcePairData G A B,
      (∀ ew ∈ owners,
        Set.InjOn (route ew) (Ωactive.filter (rowPred ew))) ∧
        (∀ ew ∈ owners,
          ∀ m ∈ Ωactive.filter (rowPred ew),
            supportOf (route ew m).1 = {ew}) ∧
          ∀ ew ∈ owners,
            ∀ m ∈ Ωactive.filter (rowPred ew),
              F m ≤ c * edgeCopySourcePairDataWeight G β J (route ew m) := by
  classical
  let route :
      ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        edgeCopySourcePairData G A B :=
    fun ew m => edgeCopySourcePairData_of_witness G (hwitness ew m)
  refine ⟨route, ?_, ?_, ?_⟩
  · intro ew hew
    exact
      edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
        G (fun m => witness ew m) (fun m => hwitness ew m)
        (hinj ew hew)
  · intro ew hew m hm
    simpa [route] using hsupport ew hew m hm
  · intro ew hew m hm
    simpa [route] using hpoint ew hew m hm

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_ownerIndexed_routes_of_sourceEquation_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    (Ωactive : Finset (↥G.edgeFinset → ℕ))
    (owners : Finset ↥G.edgeFinset)
    (rowPred : ↥G.edgeFinset → (↥G.edgeFinset → ℕ) → Prop)
    [∀ ew, DecidablePred (rowPred ew)]
    (supportOf : (↥G.edgeFinset → ℕ) → Finset ↥G.edgeFinset)
    (F : (↥G.edgeFinset → ℕ) → ℝ)
    (profileRoute :
      ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        (↥G.edgeFinset → ℕ))
    (witness :
      (ew : ↥G.edgeFinset) → (m : ↥G.edgeFinset → ℕ) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute ew m)))
    (hleft :
      ∀ ew m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute ew m))
          (witness ew m) =
          A)
    (hright :
      ∀ ew m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute ew m))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute ew m))) \
            witness ew m) =
          B)
    (hinj :
      ∀ ew ∈ owners,
        Set.InjOn (profileRoute ew) (Ωactive.filter (rowPred ew)))
    (hsupport :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (rowPred ew),
          supportOf (profileRoute ew m) = {ew})
    (hpoint :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (rowPred ew),
          F m ≤
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute ew m))) :
    ∃ route :
        ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
          edgeCopySourcePairData G A B,
      (∀ ew ∈ owners,
        Set.InjOn (route ew) (Ωactive.filter (rowPred ew))) ∧
        (∀ ew ∈ owners,
          ∀ m ∈ Ωactive.filter (rowPred ew),
            supportOf (route ew m).1 = {ew}) ∧
          ∀ ew ∈ owners,
            ∀ m ∈ Ωactive.filter (rowPred ew),
              F m ≤ c * edgeCopySourcePairDataWeight G β J (route ew m) := by
  refine
    edgeCopySourcePairData_ownerIndexed_routes_of_profileWitness_routes
      G β J c Ωactive owners rowPred supportOf F profileRoute witness ?_
      hinj hsupport hpoint
  intro ew m
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft ew m, hright ew m⟩

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_positiveMultiplicityIndexed_routes_of_profileWitness_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    (Ωactive : Finset (↥G.edgeFinset → ℕ))
    (owners : Finset ↥G.edgeFinset)
    (supportOf : (↥G.edgeFinset → ℕ) → Finset ↥G.edgeFinset)
    (F : (↥G.edgeFinset → ℕ) → ℝ)
    (profileRoute :
      ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        (↥G.edgeFinset → ℕ))
    (witness :
      (ew : ↥G.edgeFinset) → (m : ↥G.edgeFinset → ℕ) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute ew m)))
    (hwitness :
      ∀ ew m,
        witness ew m ∈ edgeCopySourcePairWitnesses G A B
          (profileRoute ew m))
    (hinj :
      ∀ ew ∈ owners,
        Set.InjOn (profileRoute ew) (Ωactive.filter (fun m => m ew ≠ 0)))
    (hsupport :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
          supportOf (profileRoute ew m) = {ew})
    (hpoint :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
          F m ≤
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute ew m))) :
    ∃ route :
        ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
          edgeCopySourcePairData G A B,
      (∀ ew ∈ owners,
        Set.InjOn (route ew) (Ωactive.filter (fun m => m ew ≠ 0))) ∧
        (∀ ew ∈ owners,
          ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
            supportOf (route ew m).1 = {ew}) ∧
          ∀ ew ∈ owners,
            ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
              F m ≤ c * edgeCopySourcePairDataWeight G β J (route ew m) := by
  classical
  let rowPred : ↥G.edgeFinset → (↥G.edgeFinset → ℕ) → Prop :=
    fun ew m => m ew ≠ 0
  simpa [rowPred] using
    edgeCopySourcePairData_ownerIndexed_routes_of_profileWitness_routes
      G β J c Ωactive owners rowPred supportOf F profileRoute witness
      hwitness hinj hsupport hpoint

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_positiveMultiplicityIndexed_routes_of_sourceEquation_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    (Ωactive : Finset (↥G.edgeFinset → ℕ))
    (owners : Finset ↥G.edgeFinset)
    (supportOf : (↥G.edgeFinset → ℕ) → Finset ↥G.edgeFinset)
    (F : (↥G.edgeFinset → ℕ) → ℝ)
    (profileRoute :
      ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        (↥G.edgeFinset → ℕ))
    (witness :
      (ew : ↥G.edgeFinset) → (m : ↥G.edgeFinset → ℕ) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute ew m)))
    (hleft :
      ∀ ew m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute ew m))
          (witness ew m) =
          A)
    (hright :
      ∀ ew m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (profileRoute ew m))
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute ew m))) \
            witness ew m) =
          B)
    (hinj :
      ∀ ew ∈ owners,
        Set.InjOn (profileRoute ew) (Ωactive.filter (fun m => m ew ≠ 0)))
    (hsupport :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
          supportOf (profileRoute ew m) = {ew})
    (hpoint :
      ∀ ew ∈ owners,
        ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
          F m ≤
            c * Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (profileRoute ew m))) :
    ∃ route :
        ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
          edgeCopySourcePairData G A B,
      (∀ ew ∈ owners,
        Set.InjOn (route ew) (Ωactive.filter (fun m => m ew ≠ 0))) ∧
        (∀ ew ∈ owners,
          ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
            supportOf (route ew m).1 = {ew}) ∧
          ∀ ew ∈ owners,
            ∀ m ∈ Ωactive.filter (fun m => m ew ≠ 0),
              F m ≤ c * edgeCopySourcePairDataWeight G β J (route ew m) := by
  classical
  let rowPred : ↥G.edgeFinset → (↥G.edgeFinset → ℕ) → Prop :=
    fun ew m => m ew ≠ 0
  simpa [rowPred] using
    edgeCopySourcePairData_ownerIndexed_routes_of_sourceEquation_routes
      G β J c Ωactive owners rowPred supportOf F profileRoute witness
      hleft hright hinj hsupport hpoint

set_option linter.style.longLine false in


theorem
    edgeCopySourcePairData_supportPattern_routes_of_profileWitness_singleton_multi_checks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    (Ωactive : Finset (↥G.edgeFinset → ℕ))
    (supportPatterns : Finset (Finset ↥G.edgeFinset))
    (supportOf : (↥G.edgeFinset → ℕ) → Finset ↥G.edgeFinset)
    (F : (↥G.edgeFinset → ℕ) → ℝ)
    (hpatterns_nonempty : ∀ S ∈ supportPatterns, S.Nonempty)
    (profileRoute :
      Finset ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
        (↥G.edgeFinset → ℕ))
    (witness :
      (S : Finset ↥G.edgeFinset) → (m : ↥G.edgeFinset → ℕ) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute S m)))
    (hwitness :
      ∀ S m,
        witness S m ∈ edgeCopySourcePairWitnesses G A B (profileRoute S m))
    (hsingle :
      ∀ S ∈ supportPatterns,
        S.card = 1 →
          Set.InjOn (profileRoute S)
              (Ωactive.filter (fun m => supportOf m = S)) ∧
            (∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
              supportOf (profileRoute S m) = S) ∧
              ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
                F m ≤
                  c * Sharpness.weight G β J
                    (Sharpness.ofEdgeFun G (profileRoute S m)))
    (hmulti :
      ∀ S ∈ supportPatterns,
        1 < S.card →
          Set.InjOn (profileRoute S)
              (Ωactive.filter (fun m => supportOf m = S)) ∧
            (∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
              supportOf (profileRoute S m) = S) ∧
              ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
                F m ≤
                  c * Sharpness.weight G β J
                    (Sharpness.ofEdgeFun G (profileRoute S m))) :
    ∃ route :
        Finset ↥G.edgeFinset → (↥G.edgeFinset → ℕ) →
          edgeCopySourcePairData G A B,
      (∀ S ∈ supportPatterns,
        Set.InjOn (route S)
          (Ωactive.filter (fun m => supportOf m = S))) ∧
        (∀ S ∈ supportPatterns,
          ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
            supportOf (route S m).1 = S) ∧
          ∀ S ∈ supportPatterns,
            ∀ m ∈ Ωactive.filter (fun m => supportOf m = S),
              F m ≤ c * edgeCopySourcePairDataWeight G β J (route S m) := by
  refine
    edgeCopySourcePairData_supportPattern_routes_of_profileWitness_routes
      G β J c Ωactive supportPatterns supportOf F profileRoute witness
      hwitness ?_ ?_ ?_
  · intro S hS
    by_cases hcard : S.card = 1
    · exact (hsingle S hS hcard).1
    · have hcard_pos : 0 < S.card := Finset.Nonempty.card_pos
        (hpatterns_nonempty S hS)
      have hcard_multi : 1 < S.card := by omega
      exact (hmulti S hS hcard_multi).1
  · intro S hS
    by_cases hcard : S.card = 1
    · exact (hsingle S hS hcard).2.1
    · have hcard_pos : 0 < S.card := Finset.Nonempty.card_pos
        (hpatterns_nonempty S hS)
      have hcard_multi : 1 < S.card := by omega
      exact (hmulti S hS hcard_multi).2.1
  · intro S hS
    by_cases hcard : S.card = 1
    · exact (hsingle S hS hcard).2.2
    · have hcard_pos : 0 < S.card := Finset.Nonempty.card_pos
        (hpatterns_nonempty S hS)
      have hcard_multi : 1 < S.card := by omega
      exact (hmulti S hS hcard_multi).2.2

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_eq_sum_sourcePairWitnesses_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) :
    (edgeCopySourceSector G A m).card =
      ∑ B : Finset V, (edgeCopySourcePairWitnesses G A B m).card := by
  classical
  let C := Sharpness.FluxEdgeCopy.Copy G m
  let S := edgeCopySourceSector G A m
  let compSrc : Finset C → Finset V :=
    fun K =>
      Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m)
        ((Finset.univ : Finset C) \ K)
  have hwitness :
      ∀ B : Finset V,
        edgeCopySourcePairWitnesses G A B m =
          S.filter (fun K => compSrc K = B) := by
    intro B
    ext K
    constructor
    · intro hK
      have h := (edgeCopySourcePairWitnesses_mem G A B m K).mp hK
      rw [Finset.mem_filter]
      exact
        ⟨(mem_edgeCopySourceSector (G := G) (A := A) (m := m)).mpr h.1,
          by simpa [compSrc, C] using h.2⟩
    · intro hK
      rw [Finset.mem_filter] at hK
      rw [edgeCopySourcePairWitnesses_mem]
      exact
        ⟨(mem_edgeCopySourceSector (G := G) (A := A) (m := m)).mp hK.1,
          by simpa [compSrc, C] using hK.2⟩
  calc
    (edgeCopySourceSector G A m).card = ∑ K ∈ S, (1 : ℕ) := by
      simp [S]
    _ = ∑ B : Finset V, ∑ K ∈ S.filter (fun K => compSrc K = B), (1 : ℕ) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := S) (t := (Finset.univ : Finset (Finset V))) (g := compSrc)
        (fun K _hK => Finset.mem_univ (compSrc K))
        (fun _K => (1 : ℕ))]
    _ = ∑ B : Finset V, (edgeCopySourcePairWitnesses G A B m).card := by
      refine Finset.sum_congr rfl ?_
      intro B _hB
      rw [hwitness B]
      simp

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_mem_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (d : edgeCopySourcePairData G A B) :
    d.2.1 ∈ edgeCopySourcePairWitnesses G A B d.1 := by
  rw [edgeCopySourcePairWitnesses_mem]
  exact d.2.2

set_option linter.style.longLine false in


theorem edgeCopySourcePairData_profileWitness_routes_of_data_routes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (β : ℝ) (J : Sym2 V → ℝ) (c : ℝ)
    {ι : Type*} (F : ι → ℝ)
    (route : ι → edgeCopySourcePairData G A B)
    (hpoint :
      ∀ i, F i ≤ c * edgeCopySourcePairDataWeight G β J (route i)) :
    ∃ profileRoute : ι → ↥G.edgeFinset → ℕ,
      ∃ witness :
          (i : ι) →
            Finset (Sharpness.FluxEdgeCopy.Copy G (profileRoute i)),
        (∀ i,
          witness i ∈ edgeCopySourcePairWitnesses G A B
            (profileRoute i)) ∧
          (∀ i, profileRoute i = (route i).1) ∧
            ∀ i,
              F i ≤
                c * Sharpness.weight G β J
                  (Sharpness.ofEdgeFun G (profileRoute i)) := by
  refine ⟨fun i => (route i).1, fun i => (route i).2.1, ?_, ?_, ?_⟩
  · intro i
    exact edgeCopySourcePairData_mem_witnesses G (route i)
  · intro i
    rfl
  · intro i
    simpa [edgeCopySourcePairDataWeight] using hpoint i

end Exact3D
end StatMech
