module
public import Swanepoel.BlockTrackLeafClassification
public import Swanepoel.LeafCountConservation
public import Swanepoel.LeafTrackConcreteTransfer
@[expose] public section

noncomputable section
namespace Swanepoel
namespace PennyGraph
variable {n : ℕ} (G : PennyGraph n)

theorem disjoint_bound_of_leaf_restrict (ht : G.TriangleFree) (hc : G.graph.Connected)
    (v a : Fin n) (ha : G.graph.Adj v a) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (hrec : (componentSystem (G.eraseVertex v) (G.eraseVertex_triangleFree ht v)
      (G.eraseVertex v).ordinaryTrackComponents
      ((G.eraseVertex v).faceDefectCount (G.eraseVertex_triangleFree ht v))).DisjointBound) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound :=
  G.disjoint_bound_of_component_erase_isolated (G.eraseVertex v) ht (G.eraseVertex_triangleFree ht v)
    (G.leafTrack v a ha) (G.eraseComponentMap v)
    (G.eraseComponentMap_injective v a hunique) (G.eraseComponentMap_image v a ha hunique)
    (fun c d => (G.eraseComponentMap_crossing_iff v a hunique c d).symm)
    (G.eraseComponentMap_terminal_iff hc v a ha hunique)
    (G.eraseVertex_defect_count ht hc v a ha hunique (G.eraseVertex_component_count v a ha hunique))
    (G.leafTrack_isolated v a ha hunique) hrec

end PennyGraph
end Swanepoel
