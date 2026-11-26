module
public import Swanepoel.PolygonSeparationProof
public import Swanepoel.DefectFreeCanonical
public import Swanepoel.DisjointReduction
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.edge_bound_of_defect_free {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected) (hf : G.faceDefectCount ht=0) :
    (G.edgeCount : ℤ)≤extremalValue n := by
  apply geometric_defect_free_upper_bound G ht
  have he := G.euler_with_defects_of_connected ht hc
  simpa only [hf,Nat.add_zero,Nat.cast_add,Nat.cast_zero,add_zero] using he

theorem PennyGraph.edge_bound_of_crossing_and_disjoint {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hpair : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).CrossingPairBound)
    (hdis : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound) :
    (G.edgeCount : ℤ)≤extremalValue n := by
  let C := geometricBlockCounts G ht (G.faceDefectCount ht)
    (G.euler_with_defects_of_connected ht hc) (G.geometric_effective_nonneg ht)
  have h := TrackSystem.rhombi_bound _
    (componentSystem_noTriple G ht G.ordinaryTrackComponents (G.faceDefectCount ht)) hpair hdis
  rw [componentSystem_q_eq_rhombi G ht G.ordinaryTrackComponents (G.faceDefectCount ht),
    componentSystem_effective_count G ht G.ordinaryTrackComponents (G.faceDefectCount ht)] at h
  exact block_bound C h

theorem PennyGraph.edge_bound_of_three_track_estimates {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hpair : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).CrossingPairBound)
    (hquad : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound)
    (hcut : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).HighCrossingCap) :
    (G.edgeCount : ℤ)≤extremalValue n :=
  G.edge_bound_of_crossing_and_disjoint ht hc hpair
    (G.canonical_disjoint_bound_of_high_crossing_cap ht hquad hcut)

end Swanepoel
