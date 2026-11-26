module
public import Swanepoel.RecursiveCutDecomposition
public import Swanepoel.CutHalfAccounting
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace CutPiece
def terminalCount (P : CutPiece) : ℕ := P.graph.terminalTrackComponents.card

def K (P : CutPiece) : ℤ :=
  (componentSystem P.graph P.triangleFree P.graph.ordinaryTrackComponents P.defects).K

def R (P : CutPiece) : ℤ :=
  (componentSystem P.graph P.triangleFree P.graph.ordinaryTrackComponents P.defects).r+P.defects

theorem K_eq (P : CutPiece) : P.K=(P.terminalCount : ℤ)-2*P.defects :=
  P.graph.componentSystem_K_eq P.triangleFree P.defects

theorem child_K_conservation (P : CutPiece) (c : P.Cut) :
    (P.child c false).K+(P.child c true).K=P.K+
      ((P.banks c).splitTerminalJoins P.triangleFree).card :=
  ((P.banks c).canonical_cut_conservation P.triangleFree P.connected
    (Finset.mem_filter.mp c.property).1).1

theorem child_terminal_count_conservation (P : CutPiece) (c : P.Cut) :
    (P.child c false).terminalCount+(P.child c true).terminalCount=P.terminalCount+
      ((P.banks c).splitTerminalJoins P.triangleFree).card := by
  have hK := P.child_K_conservation c
  have hf := P.child_defects_sum c
  have hL := (P.child c false).K_eq
  have hR := (P.child c true).K_eq
  have hP := P.K_eq
  omega

theorem child_R_allocation (P : CutPiece) (c : P.Cut) :
    P.R=(P.child c false).R+(P.banks c).inheritedNonAnchorCrossings P.triangleFree false+
      (P.child c true).R+(P.banks c).inheritedNonAnchorCrossings P.triangleFree true :=
  (P.banks c).canonical_cut_R_allocation P.triangleFree P.connected
    (Finset.mem_filter.mp c.property).1

end CutPiece

namespace CompleteCutTree
def nodeSplitJoins (N : CutNode) : ℕ :=
  ((N.1.banks N.2).splitTerminalJoins N.1.triangleFree).card

def nodeInheritedCrossings (N : CutNode) : ℤ :=
  (N.1.banks N.2).inheritedNonAnchorCrossings N.1.triangleFree false+
    (N.1.banks N.2).inheritedNonAnchorCrossings N.1.triangleFree true

theorem leaves_terminal_count_conservation {P : CutPiece} (t : CompleteCutTree P) :
    (t.leaves.map CutPiece.terminalCount).sum=P.terminalCount+(t.nodes.map nodeSplitJoins).sum := by
  induction t with
  | leaf _ => simp [leaves,nodes]
  | @node P c L R ihL ihR =>
    simp only [leaves,nodes,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    have h := P.child_terminal_count_conservation c
    change _=P.terminalCount+nodeSplitJoins ⟨P,c⟩ at h
    omega

theorem leaves_K_conservation {P : CutPiece} (t : CompleteCutTree P) :
    (t.leaves.map CutPiece.K).sum=P.K+((t.nodes.map nodeSplitJoins).sum : ℤ) := by
  induction t with
  | leaf _ => simp [leaves,nodes]
  | @node P c L R ihL ihR =>
    simp only [leaves,nodes,List.map_append,List.sum_append,List.map_cons,List.sum_cons,Nat.cast_add]
    have h := P.child_K_conservation c
    change _=P.K+(nodeSplitJoins ⟨P,c⟩ : ℤ) at h
    omega

theorem leaves_R_allocation {P : CutPiece} (t : CompleteCutTree P) :
    P.R=(t.leaves.map CutPiece.R).sum+(t.nodes.map nodeInheritedCrossings).sum := by
  induction t with
  | leaf _ => simp [leaves,nodes]
  | @node P c L R ihL ihR =>
    simp only [leaves,nodes,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    have h := P.child_R_allocation c
    have hN : nodeInheritedCrossings ⟨P,c⟩=
        ((P.banks c).inheritedNonAnchorCrossings P.triangleFree false : ℤ)+
        (P.banks c).inheritedNonAnchorCrossings P.triangleFree true := rfl
    omega

end CompleteCutTree
end Swanepoel
