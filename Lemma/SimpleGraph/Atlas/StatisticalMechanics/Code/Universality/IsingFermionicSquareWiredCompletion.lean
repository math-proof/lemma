import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
open StatMech StatMech.Universality


/--
[fkIsingSquareLeftVerticalUpper_south_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareLeftVerticalUpper_south_available_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareLeftVerticalUpper n hn k) .south := by
-- proof
  apply StatMech.Universality.fkIsingSquareLeftVerticalUpper_south_available n hn k

/--
[fkIsingSquareLeftVerticalLower_north_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareLeftVerticalLower_north_available_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareLeftVerticalLower n hn k) .north := by
-- proof
  apply StatMech.Universality.fkIsingSquareLeftVerticalLower_north_available n hn k

/--
[fkIsingSquareMarkedB_east_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareMarkedB_east_available_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareMarkedB n) .east := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedB_east_available n hn

/--
[fkIsingSquareMarkedA_east_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareMarkedA_east_available_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareMarkedA n) .east := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedA_east_available n hn

/--
[fkIsingSquareDirectionDart_endpoint_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareDirectionDart_endpoint_congr_eq
  {n : Nat}
  {u v : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn}
-- given
  (h : u = v)
  (hu : fkIsingSquareDirectionAvailable n u d)
  (hv : fkIsingSquareDirectionAvailable n v d) :
-- imply
  fkIsingSquareDirectionDart n u d hu turn = fkIsingSquareDirectionDart n v d hv turn := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionDart_endpoint_congr n h d hu hv turn

/--
[fkIsingSquareDart_key_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareDart_key_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) => (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d, d.2)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareDart_key_injective n

/--
[fkIsingSquareWiredBoundaryDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryDart_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fkIsingSquareWiredBoundaryDart n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryDart_injective n hn

/--
[fkIsingSquareWiredShift_left_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredShift_left_inv_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.LeftInverse (fkIsingSquareWiredShiftInv n hn) (fkIsingSquareWiredShift n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredShift_left_inv n hn

/--
[fkIsingSquareWiredShift_right_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredShift_right_inv_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.RightInverse (fkIsingSquareWiredShiftInv n hn) (fkIsingSquareWiredShift n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredShift_right_inv n hn

/--
[fkIsingSquareWiredBondMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_involutive_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Involutive (fkIsingSquareWiredBondMate n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_involutive n hn

/--
[fkIsingSquareWiredBondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_ne_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn d ≠ d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_ne n hn d

/--
[fkIsingSquareBondMate_wired_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_wired_bottom_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareWiredBoundaryDart n hn .bottom) = fkIsingSquareWiredBoundaryDart n hn (.west ⟨0, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_wired_bottom n hn

/--
[fkIsingSquareBondMate_wired_west_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_wired_west_zero_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareWiredBoundaryDart n hn (.west ⟨0, by omega⟩)) = fkIsingSquareWiredBoundaryDart n hn .bottom := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_wired_west_zero n hn

/--
[fkIsingSquareBondMate_wired_west_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_wired_west_succ_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hk : k.val ≠ 0) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareWiredBoundaryDart n hn (.west k)) = fkIsingSquareWiredBoundaryDart n hn (.north ⟨k.val - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_wired_west_succ n hn k hk

/--
[fkIsingSquareBondMate_wired_north_not_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_wired_north_not_last_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hk : k.val + 1 < 2 * n) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareWiredBoundaryDart n hn (.north k)) = fkIsingSquareWiredBoundaryDart n hn (.west ⟨k.val + 1, hk⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_wired_north_not_last n hn k hk

/--
[fkIsingSquareBondMate_wired_north_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_wired_north_last_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hk : ¬k.val + 1 < 2 * n) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareWiredBoundaryDart n hn (.north k)) = fkIsingSquareWiredBoundaryDart n hn .top := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_wired_north_last n hn k hk

/--
[fkIsingSquareBondMate_wired_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_wired_top_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareWiredBoundaryDart n hn .top) = fkIsingSquareWiredBoundaryDart n hn (.north ⟨2 * n - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_wired_top n hn

/--
[fkIsingSquareWiredShiftDartEquiv_apply_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredShiftDartEquiv_apply_boundary_eq
  {n : Nat}
  {i : FKIsingSquareWiredBoundaryDartIndex n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredShiftDartEquiv n hn (fkIsingSquareWiredBoundaryDart n hn i) = fkIsingSquareWiredBoundaryDart n hn (fkIsingSquareWiredShift n hn i) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredShiftDartEquiv_apply_boundary n hn i

/--
[fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary_eq
  {n : Nat}
  {i : FKIsingSquareWiredBoundaryDartIndex n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredShiftDartEquiv n hn).symm (fkIsingSquareWiredBoundaryDart n hn i) = fkIsingSquareWiredBoundaryDart n hn (fkIsingSquareWiredShiftInv n hn i) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary n hn i

/--
[fkIsingSquareWiredBondMate_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_bottom_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (fkIsingSquareWiredBoundaryDart n hn .bottom) = fkIsingSquareWiredBoundaryDart n hn .top := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_bottom n hn

/--
[fkIsingSquareWiredBondMate_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_top_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (fkIsingSquareWiredBoundaryDart n hn .top) = fkIsingSquareWiredBoundaryDart n hn .bottom := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_top n hn

/--
[fkIsingSquareWiredBondMate_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_west_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (fkIsingSquareWiredBoundaryDart n hn (.west k)) = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_west n hn k

/--
[fkIsingSquareWiredBondMate_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_north_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondMate n hn (fkIsingSquareWiredBoundaryDart n hn (.north k)) = fkIsingSquareWiredBoundaryDart n hn (.west k) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_north n hn k

/--
[fkIsingSquareWiredIncidenceMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredIncidenceMate_involutive_eq
  {n : Nat} :
-- imply
  Function.Involutive (fkIsingSquareWiredIncidenceMate n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIncidenceMate_involutive n

/--
[fkIsingSquareWiredSourceDart_ne_terminalDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredSourceDart_ne_terminalDart_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredSourceDart n hn ≠ fkIsingSquareWiredTerminalDart n hn := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSourceDart_ne_terminalDart n hn

/--
[fkIsingSquareWiredTransitionMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionMate_involutive_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  Function.Involutive (fkIsingSquareWiredTransitionMate n hn omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionMate_involutive n hn omega

/--
[fkIsingSquareWiredTransitionMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionMate_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredTransitionMate n hn omega x ≠ x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionMate_ne n hn omega x

/--
[fkIsingSquareWiredIncidenceMate_ne_transitionMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredIncidenceMate_ne_transitionMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hsource : x ≠ .source)
  (hterminal : x ≠ .terminal) :
-- imply
  fkIsingSquareWiredIncidenceMate n x ≠ fkIsingSquareWiredTransitionMate n hn omega x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIncidenceMate_ne_transitionMate n hn omega x hsource hterminal

/--
[fkIsingSquareWiredLoopGraph_adj_source_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_adj_source_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).Adj .source z ↔ z = .bond (fkIsingSquareWiredSourceDart n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_adj_source_iff n hn omega z

/--
[fkIsingSquareWiredLoopGraph_adj_terminal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_adj_terminal_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).Adj .terminal z ↔ z = .bond (fkIsingSquareWiredTerminalDart n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_adj_terminal_iff n hn omega z

/--
[fkIsingSquareWiredLoopGraph_source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_source_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).degree .source = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_source_degree n hn omega

/--
[fkIsingSquareWiredLoopGraph_terminal_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_terminal_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).degree .terminal = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_terminal_degree n hn omega

/--
[fkIsingSquareWiredLoopGraph_internal_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_internal_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hsource : x ≠ .source)
  (hterminal : x ≠ .terminal) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).degree x = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_internal_degree n hn omega x hsource hterminal

/--
[fkIsingSquareWiredLoopGraph_source_reachable_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_source_reachable_terminal_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source .terminal := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega

/--
[fkIsingSquareWiredExplorationOrder_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredExplorationOrder_nodup_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredExplorationOrder n hn omega).Nodup := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExplorationOrder_nodup n hn omega

/--
[mem_fkIsingSquareWiredExplorationTrace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma mem_fkIsingSquareWiredExplorationTrace_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  z ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔ (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.mem_fkIsingSquareWiredExplorationTrace_iff n hn omega z

/--
[fkIsingSquareWired_localMate_mem_trace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_localMate_mem_trace_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (FKIsingMedialDart.localMate omega d) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔ (.dart d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_localMate_mem_trace_iff n hn omega d

/--
[fkIsingSquareWired_closed_west_mem_iff_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_west_mem_iff_south_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ↔ (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_west_mem_iff_south n hn omega e

/--
[fkIsingSquareWired_closed_east_mem_iff_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_east_mem_iff_north_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ↔ (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_east_mem_iff_north n hn omega e

/--
[fkIsingSquareWired_open_west_mem_iff_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_west_mem_iff_north_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) ↔ (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_west_mem_iff_north n hn omega e

/--
[fkIsingSquareWired_open_east_mem_iff_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_east_mem_iff_south_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) ↔ (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_east_mem_iff_south n hn omega e

/--
[fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) = medialTwoEdgeSwitch (fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)) (.dart (e, .west)) (.dart (e, .south)) (.dart (e, .east)) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e

/--
[fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable .source z ↔ (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff n hn omega z

/--
[fkIsingSquareWiredCompletedLoopGraph_source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_source_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree .source = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_source_degree n hn omega

/--
[fkIsingSquareWiredCompletedLoopGraph_terminal_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_terminal_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree .terminal = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_terminal_degree n hn omega

/--
[fkIsingSquareWiredCompletedLoopGraph_internal_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_internal_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hsource : x ≠ .source)
  (hterminal : x ≠ .terminal) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_internal_degree n hn omega x hsource hterminal

/--
[fkIsingSquareWiredCompletedLoopGraph_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_even_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  Even ((fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_even_degree n hn omega x

/--
[fkIsingSquareWiredCompletedLoopGraph_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_degree_eq_two_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn omega x

/--
[fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredCompletedLoopGraph n hn (setOpen e.1 omega) = medialTwoEdgeSwitch (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)) (.dart (e, .west)) (.dart (e, .south)) (.dart (e, .east)) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e

/--
[fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj n hn omega e

/--
[fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj n hn omega e

/--
[fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
  (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
-- imply
  ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east n hn omega e hwest heast

/--
[fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
  (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
-- imply
  ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west n hn omega e heast hwest

/--
[fkIsingSquareWired_open_local_not_mem_of_closed_west_east_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_local_not_mem_of_closed_west_east_not_mem_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
  (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
-- imply
  ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_local_not_mem_of_closed_west_east_not_mem n hn omega e hwest heast

/--
[fkIsingSquareWired_local_switch_component_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_local_switch_component_classification_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧ ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨ ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧ ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨ ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧ ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨ ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_local_switch_component_classification n hn omega e

/--
[fkIsingSquareWiredPath_mem_support_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredPath_mem_support_iff_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {p : (fkIsingSquareWiredLoopGraph n hn omega).Walk (.source : FKIsingSquareWiredCarrier n) .terminal}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hp : p.IsPath) :
-- imply
  z ∈ p.support ↔ (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPath_mem_support_iff_reachable n hn omega p hp z

/--
[mem_fkIsingSquareWiredExplorationOrder_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma mem_fkIsingSquareWiredExplorationOrder_iff_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  z ∈ fkIsingSquareWiredExplorationOrder n hn omega ↔ (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.mem_fkIsingSquareWiredExplorationOrder_iff_reachable n hn omega z

/--
[mem_fkIsingSquareWiredExplorationOrder_iff_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma mem_fkIsingSquareWiredExplorationOrder_iff_trace_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  z ∈ fkIsingSquareWiredExplorationOrder n hn omega ↔ z ∈ fkIsingSquareWiredExplorationTrace n hn omega := by
-- proof
  apply StatMech.Universality.mem_fkIsingSquareWiredExplorationOrder_iff_trace n hn omega z

/--
[fkIsingSquareWired_sourceTerminalPath_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_sourceTerminalPath_unique_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {p q : (fkIsingSquareWiredLoopGraph n hn omega).Walk (.source : FKIsingSquareWiredCarrier n) .terminal}
-- given
  (hn : 0 < n)
  (hp : p.IsPath)
  (hq : q.IsPath) :
-- imply
  p = q := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_sourceTerminalPath_unique n hn omega p q hp hq

/--
[fkIsingSquareWiredExplorationPath_mem_edges_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredExplorationPath_mem_edges_of_adj_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hx : x ∈ fkIsingSquareWiredExplorationOrder n hn omega)
  (hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
-- imply
  s(x, y) ∈ (fkIsingSquareWiredExplorationPath n hn omega : (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExplorationPath_mem_edges_of_adj n hn omega hx hadj

/--
[fkIsingSquareWired_localMate_infix_explorationOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_localMate_infix_explorationOrder_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
-- imply
  [(.dart (e, side) : FKIsingSquareWiredCarrier n), .dart (FKIsingMedialDart.localMate omega (e, side))] <:+: fkIsingSquareWiredExplorationOrder n hn omega ∨ [(.dart (FKIsingMedialDart.localMate omega (e, side)) : FKIsingSquareWiredCarrier n), .dart (e, side)] <:+: fkIsingSquareWiredExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_localMate_infix_explorationOrder n hn omega e side h

/--
[fkIsingSquareWiredExplorationOrder_source_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredExplorationOrder_source_mem_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (.source : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExplorationOrder_source_mem n hn omega

/--
[fkIsingSquareWiredExplorationOrder_terminal_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredExplorationOrder_terminal_mem_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (.terminal : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExplorationOrder_terminal_mem n hn omega

/--
[fkIsingSquareWiredTransitionTurn_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionTurn_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredTransitionTurn n hn omega (.dart d) (.dart (FKIsingMedialDart.localMate omega d)) = fkIsingSquareSignedEighthTurn (fkIsingSquareWiredCarrierTangentCode n hn (.dart d) + 4) (fkIsingSquareWiredCarrierTangentCode n hn (.dart (FKIsingMedialDart.localMate omega d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionTurn_localMate n hn omega d

/--
[fkIsingSquareWiredTransitionTurn_local_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionTurn_local_table_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .west)) (.dart (e, .south)) = -2) ∧ (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .south)) (.dart (e, .west)) = 2) ∧ (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .east)) (.dart (e, .north)) = -2) ∧ (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .north)) (.dart (e, .east)) = 2) ∧ (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .west)) (.dart (e, .north)) = 2) ∧ (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .north)) (.dart (e, .west)) = -2) ∧ (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .east)) (.dart (e, .south)) = 2) ∧ (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .south)) (.dart (e, .east)) = -2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionTurn_local_table n hn omega e

/--
[fkIsingSquareWiredRawTurnCount_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredRawTurnCount_succ_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hi : i + 1 < (fkIsingSquareWiredExplorationOrder n hn omega).length) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn omega (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] = fkIsingSquareWiredRawTurnCount n hn omega (fkIsingSquareWiredExplorationOrder n hn omega)[i] + fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredExplorationOrder n hn omega)[i] (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRawTurnCount_succ n hn omega i hi

/--
[fkIsingSquareWiredRawTurnCount_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredRawTurnCount_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
-- imply
  (fkIsingSquareWiredRawTurnCount n hn omega (.dart (FKIsingMedialDart.localMate omega (e, side))) = fkIsingSquareWiredRawTurnCount n hn omega (.dart (e, side)) + fkIsingSquareWiredTransitionTurn n hn omega (.dart (e, side)) (.dart (FKIsingMedialDart.localMate omega (e, side)))) ∨ (fkIsingSquareWiredRawTurnCount n hn omega (.dart (e, side)) = fkIsingSquareWiredRawTurnCount n hn omega (.dart (FKIsingMedialDart.localMate omega (e, side))) + fkIsingSquareWiredTransitionTurn n hn omega (.dart (FKIsingMedialDart.localMate omega (e, side))) (.dart (e, side))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRawTurnCount_localMate n hn omega e side h

/--
[fkIsingSquareWired_closed_west_south_rawTurnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_west_south_rawTurnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega) (.dart (e, .south)) = fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega) (.dart (e, .west)) - 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_west_south_rawTurnCount n hn omega e h

/--
[fkIsingSquareWired_closed_east_north_rawTurnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_east_north_rawTurnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega) (.dart (e, .north)) = fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega) (.dart (e, .east)) - 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_east_north_rawTurnCount n hn omega e h

/--
[fkIsingSquareWired_open_west_north_rawTurnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_west_north_rawTurnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega) (.dart (e, .north)) = fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega) (.dart (e, .west)) + 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_west_north_rawTurnCount n hn omega e h

/--
[fkIsingSquareWired_open_east_south_rawTurnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_east_south_rawTurnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega) (.dart (e, .south)) = fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega) (.dart (e, .east)) + 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_east_south_rawTurnCount n hn omega e h

/--
[fkIsingSquareWired_closed_west_south_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_west_south_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .south)) = fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .west)) - Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_west_south_winding n hn omega e h

/--
[fkIsingSquareWired_closed_east_north_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_east_north_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .north)) = fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .east)) - Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_east_north_winding n hn omega e h

/--
[fkIsingSquareWired_open_west_north_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_west_north_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .north)) = fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .west)) + Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_west_north_winding n hn omega e h

/--
[fkIsingSquareWired_open_east_south_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_east_south_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .south)) = fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .east)) + Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_east_south_winding n hn omega e h

/--
[fkIsingSquareWiredLiftedWinding_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean)
-/
@[path]
private lemma fkIsingSquareWiredLiftedWinding_terminal_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn omega .terminal = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLiftedWinding_terminal n hn omega


-- created on 2026-10-23
