module
public import Swanepoel.JoinClosedDecomposition
public import Swanepoel.Counting
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.familyTrackIndices {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) :
    Finset (Fin (Fintype.card (TrackComponent G))) :=
  (G.familyTrackComponents Y).map (Fintype.equivFin (TrackComponent G)).toEmbedding

def PennyGraph.familyInternalCrossings {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) : ℕ :=
  (componentSystem G ht ∅ 0).internal (G.familyTrackIndices Y)

def PennyGraph.interFamilyCrossings {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y Z : Finset (PlaneFace G)) : ℕ :=
  (componentSystem G ht ∅ 0).crossings (G.familyTrackIndices Y) (G.familyTrackIndices Z)

theorem PennyGraph.familyTrackIndices_union {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G)) :
    G.familyTrackIndices (Y ∪ Z) = G.familyTrackIndices Y ∪ G.familyTrackIndices Z := by
  simp only [PennyGraph.familyTrackIndices, G.familyTrackComponents_union, Finset.map_union]

theorem PennyGraph.familyTrackIndices_disjoint {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    Disjoint (G.familyTrackIndices Y) (G.familyTrackIndices Z) := by
  have htracks := G.familyTrackComponents_disjoint ht hY hZ hYZ
  apply Finset.disjoint_left.mpr
  intro i hiY hiZ
  obtain ⟨c,hc,hci⟩ := Finset.mem_map.mp hiY
  obtain ⟨d,hd,hdi⟩ := Finset.mem_map.mp hiZ
  have hcd : c = d := (Fintype.equivFin (TrackComponent G)).injective (hci.trans hdi.symm)
  exact Finset.disjoint_left.mp htracks (hcd ▸ hc) hd

theorem PennyGraph.family_internal_crossings_union {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    G.familyInternalCrossings ht (Y ∪ Z) = G.familyInternalCrossings ht Y +
      G.familyInternalCrossings ht Z + G.interFamilyCrossings ht Y Z := by
  unfold PennyGraph.familyInternalCrossings PennyGraph.interFamilyCrossings
  rw [G.familyTrackIndices_union]
  exact TrackSystem.internal_union _ _ _ (G.familyTrackIndices_disjoint ht hY hZ hYZ)

end Swanepoel
