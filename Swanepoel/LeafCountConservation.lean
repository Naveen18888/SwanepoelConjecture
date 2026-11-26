module
public import Swanepoel.BlockTrackLeafGraph
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
namespace PennyGraph
variable {n : ℕ} (G : PennyGraph n)

theorem eraseVertex_rhombi_count (ht : G.TriangleFree) (v a : Fin n)
    (hva : G.graph.Adj v a) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (hT : Fintype.card (TrackComponent (G.eraseVertex v))+1=Fintype.card (TrackComponent G)) :
    Fintype.card (RhombusSet (G.eraseVertex v))=Fintype.card (RhombusSet G) := by
  have hm := G.eraseVertex_edgeCount_add_one v a hva hunique
  have hG := geometric_track_identity G ht
  have hH := geometric_track_identity (G.eraseVertex v) (G.eraseVertex_triangleFree ht v)
  omega

theorem eraseVertex_defect_count (ht : G.TriangleFree) (hc : G.graph.Connected)
    (v a : Fin n) (hva : G.graph.Adj v a) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (hT : Fintype.card (TrackComponent (G.eraseVertex v))+1=Fintype.card (TrackComponent G)) :
    (G.eraseVertex v).faceDefectCount (G.eraseVertex_triangleFree ht v)=G.faceDefectCount ht := by
  have hn := G.eraseVertex_card_add_one v
  have hm := G.eraseVertex_edgeCount_add_one v a hva hunique
  have hq := G.eraseVertex_rhombi_count ht v a hva hunique hT
  have hG := G.euler_with_defects_of_connected ht hc
  have hH := (G.eraseVertex v).euler_with_defects_of_connected
    (G.eraseVertex_triangleFree ht v) (G.eraseVertex_connected hc v a hva hunique)
  omega

end PennyGraph
end Swanepoel
