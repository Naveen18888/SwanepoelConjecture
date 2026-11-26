module
public import Swanepoel.ConnectedTrackInduction
public import Swanepoel.BlockTrackLeafTransfer
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel

theorem PennyGraph.lemma_3_1 {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound :=
  connected_disjoint_bounds_of_leaf_transport
    (fun _ H hH hconn v a hva hunique hrec =>
      H.disjoint_bound_of_leaf_restrict hH hconn v a hva hunique hrec) n G ht hc

theorem PennyGraph.CyclicBlock.lemma_3_1 {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound :=
  G.lemma_3_1 ht hb.2.1

end Swanepoel
