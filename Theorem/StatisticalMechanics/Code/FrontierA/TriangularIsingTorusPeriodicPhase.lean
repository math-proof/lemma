/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

@[simp] theorem triangularPathDisplacement_nil :
    triangularPathDisplacement [] = 0 := rfl

@[simp] theorem triangularPathDisplacement_cons
    (d : Fin 6) (ds : List (Fin 6)) :
    triangularPathDisplacement (d :: ds) =
      triangularIntStep d + triangularPathDisplacement ds := rfl

@[simp] theorem triangularPathVertices_nil :
    triangularPathVertices [] = [0] := rfl

@[simp] theorem triangularPathVertices_cons
    (d : Fin 6) (ds : List (Fin 6)) :
    triangularPathVertices (d :: ds) =
      0 :: (triangularPathVertices ds).map (triangularIntStep d + ·) := rfl

theorem triangularPathDisplacement_append (l r : List (Fin 6)) :
    triangularPathDisplacement (l ++ r) =
      triangularPathDisplacement l + triangularPathDisplacement r := by
  induction l with
  | nil => simp
  | cons d ds ih => simp only [List.cons_append,
      triangularPathDisplacement_cons, ih]; abel

@[simp] theorem triangularPathVertices_length (l : List (Fin 6)) :
    (triangularPathVertices l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

@[simp] theorem triangularPathVertices_head (l : List (Fin 6)) :
    (triangularPathVertices l).head? = some 0 := by
  cases l <;> rfl

theorem triangularPathVertices_getLast (l : List (Fin 6)) :
    (triangularPathVertices l).getLast? =
      some (triangularPathDisplacement l) := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [triangularPathVertices_cons, List.getLast?_cons,
        List.getLast?_map, ih, Option.map_some,
        triangularPathDisplacement_cons]
      simp

theorem triangularPathVertices_append (l r : List (Fin 6)) :
    triangularPathVertices (l ++ r) =
      (triangularPathVertices l).dropLast ++
        (triangularPathVertices r).map
          (triangularPathDisplacement l + ·) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      have hmap :
          (triangularPathVertices ds).map (triangularIntStep d + ·) ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_map, triangularPathVertices_length] at hlen
        simp at hlen
      simp only [List.cons_append, triangularPathVertices_cons, ih,
        List.map_append, List.map_map,
        List.dropLast_cons_of_ne_nil hmap,
        <- List.map_dropLast, triangularPathDisplacement_cons]
      congr 2
      apply List.map_congr_left
      intro z hz
      simp only [Function.comp_apply]
      abel

theorem triangularPathVertices_append_dropLast (l r : List (Fin 6)) :
    (triangularPathVertices (l ++ r)).dropLast =
      (triangularPathVertices l).dropLast ++
        (triangularPathVertices r).dropLast.map
          (triangularPathDisplacement l + ·) := by
  rw [triangularPathVertices_append]
  have hne :
      (triangularPathVertices r).map
          (triangularPathDisplacement l + ·) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [List.length_map, triangularPathVertices_length] at hlen
    simp at hlen
  rw [List.dropLast_append_of_ne_nil hne, <- List.map_dropLast]

end StatMech.FrontierA
