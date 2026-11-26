module
public import Swanepoel.CutCrossingAccounting
public import Swanepoel.CutInheritedTracks
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.componentIndices {n : ℕ} (G : PennyGraph n) (S : Finset (TrackComponent G)) :
    Finset (Fin (Fintype.card (TrackComponent G))) :=
  S.map (Fintype.equivFin (TrackComponent G)).toEmbedding

@[simp] theorem PennyGraph.mem_componentIndices {n : ℕ} (G : PennyGraph n)
    (S : Finset (TrackComponent G)) (i : Fin (Fintype.card (TrackComponent G))) :
    i∈G.componentIndices S ↔ (Fintype.equivFin (TrackComponent G)).symm i∈S := by
  simp only [PennyGraph.componentIndices,Finset.mem_map_equiv]

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def inheritedNonAnchorCrossings (ht : G.TriangleFree) (side : Bool) : ℕ :=
  (componentSystem G ht ∅ 0).crossings
    (G.componentIndices (B.inheritedNonAnchors ht side))
    (G.componentIndices (B.bankAnchorTracks ht side))

theorem terminal_crossing_allocation (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r=
      G.familyInternalCrossings ht (B.bankDefectFamily ht false)+
      G.familyInternalCrossings ht (B.bankDefectFamily ht true)+
      B.inheritedNonAnchorCrossings ht false+B.inheritedNonAnchorCrossings ht true := by
  let D := componentSystem G ht ∅ 0
  let T := G.componentIndices G.terminalTrackComponents
  let A := G.componentIndices (B.bankAnchorTracks ht false)
  let E := G.componentIndices (B.bankAnchorTracks ht true)
  let C := G.componentIndices B.terminalCutCrossers
  have hcover : A∪E=T := by
    ext i
    simp only [A,E,T,Finset.mem_union,G.mem_componentIndices]
    rw [← Finset.mem_union,B.bankAnchorTracks_union ht]
  have hC : C⊆T := by
    intro i hi
    exact (G.mem_componentIndices _ _).mpr (Finset.mem_filter.mp ((G.mem_componentIndices _ _).mp hi)).1
  have hinter : A∩E⊆C := by
    intro i hi
    have hh := Finset.mem_inter.mp hi
    apply (G.mem_componentIndices _ _).mpr
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · have hiT : i∈T := by
        rw [← hcover]
        exact Finset.mem_union_left E hh.1
      exact (G.mem_componentIndices _ _).mp hiT
    · exact B.splitTerminalJoins_cross ht hcut (Finset.mem_inter.mpr
        ⟨(G.mem_componentIndices _ _).mp hh.1,(G.mem_componentIndices _ _).mp hh.2⟩)
  have hind : D.Disjoint C := by
    intro i hi j hj hij
    have hx := (Finset.mem_filter.mp ((G.mem_componentIndices _ _).mp hi)).2
    have hy := (Finset.mem_filter.mp ((G.mem_componentIndices _ _).mp hj)).2
    exact componentGraph_noTriple G ht cut _ _ hx hij ((componentGraph G ht).adj_symm hy)
  have hsep : ∀ i∈T,∀ j∈T,D.crossing.Adj i j → i∉C → j∉C →
      (i∈A ∧ j∈A) ∨ (i∈E ∧ j∈E) := by
    intro i hi j hj hij him hjm
    have hh := B.terminal_missing_crossing_same_bank ht hcut _ _
      ((G.mem_componentIndices _ _).mp hi) ((G.mem_componentIndices _ _).mp hj) hij
      (fun h => him ((G.mem_componentIndices _ _).mpr h))
      (fun h => hjm ((G.mem_componentIndices _ _).mpr h))
    simpa only [A,E,G.mem_componentIndices] using hh
  have hf (side : Bool) :
      C\G.componentIndices (B.bankAnchorTracks ht side)=G.componentIndices (B.inheritedNonAnchors ht side) := by
    ext i
    simp only [C,Finset.mem_sdiff,G.mem_componentIndices,B.mem_inheritedNonAnchors,
      terminalCutCrossers,Finset.mem_filter]
    tauto
  have h := D.cut_internal_allocation T A E C hcover hC hinter hind hsep
  have hL : D.crossings (C\A) A=B.inheritedNonAnchorCrossings ht false :=
    congrArg (fun S : Finset D.Track => D.crossings S A) (hf false)
  have hR : D.crossings (C\E) E=B.inheritedNonAnchorCrossings ht true :=
    congrArg (fun S : Finset D.Track => D.crossings S E) (hf true)
  have hOrig : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r=D.internal T := by
    rw [← G.familyInternalCrossings_all_defects ht]
    change D.internal (G.componentIndices (G.familyTrackComponents (G.defectPlaneFaces ht)))=_
    exact congrArg D.internal (congrArg G.componentIndices (G.familyTrackComponents_all_defects ht))
  change (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r=
    D.internal A+D.internal E+B.inheritedNonAnchorCrossings ht false+B.inheritedNonAnchorCrossings ht true
  omega

theorem canonical_cut_R_allocation (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) :
    ((componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r : ℤ)+G.faceDefectCount ht=
      (B.canonicalHalfSystem ht false).R+B.inheritedNonAnchorCrossings ht false+
      (B.canonicalHalfSystem ht true).R+B.inheritedNonAnchorCrossings ht true := by
  have hr := B.terminal_crossing_allocation ht hcut
  have hf := B.bank_defect_count_conservation ht
  rw [B.canonicalHalf_R_eq_bank ht hc hcut false,B.canonicalHalf_R_eq_bank ht hc hcut true]
  unfold PennyGraph.familyR
  omega

end OrdinaryCutBanks
end Swanepoel
