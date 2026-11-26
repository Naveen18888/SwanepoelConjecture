module
public import Swanepoel.BlockTrackLeafGeometry
public import Swanepoel.LeafFaceDeletion
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PennyGraph
variable {n : ℕ} (G : PennyGraph n)

theorem eraseVertex_sourceFace_bounded_iff (hc : G.graph.Connected) (v a : Fin n)
    (ha : G.graph.Adj v a) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (e : OrientedEdge (G.eraseVertex v)) :
    Bornology.IsBounded (G.sourceFace ((G.eraseVertexEmbedding v).mapEdge e)).val ↔
      Bornology.IsBounded ((G.eraseVertex v).sourceFace e).val :=
  G.sourceFace_bounded_iff_of_drawing_subset_of_card (G.eraseVertex v)
    (G.eraseVertex_drawing_subset v) (G.eraseVertex_face_count hc v a ha hunique)
    ((G.eraseVertexEmbedding v).mapEdge e) e ((G.eraseVertexEmbedding v).mapEdge_vector e).symm rfl

theorem eraseComponentMap_terminal_iff (hc : G.graph.Connected) (v a : Fin n)
    (ha : G.graph.Adj v a) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (c : TrackComponent (G.eraseVertex v)) :
    c∈(G.eraseVertex v).terminalTrackComponents ↔ G.eraseComponentMap v c∈G.terminalTrackComponents := by
  rw [(G.eraseVertex v).terminal_iff_bounded_source,G.terminal_iff_bounded_source]
  constructor
  · rintro ⟨e,he,hec,hb⟩
    refine ⟨(G.eraseVertexEmbedding v).mapEdge e,(G.eraseSource_iff v a hunique e).mp he,?_,?_⟩
    · change G.eraseComponentMap v (edgeComponent e)=G.eraseComponentMap v c
      exact congrArg (G.eraseComponentMap v) hec
    · exact (G.eraseVertex_sourceFace_bounded_iff hc v a ha hunique e).mpr hb
  · rintro ⟨e,he,hec,hb⟩
    obtain ⟨f,hf⟩ := G.eraseComponentMap_full_retention v a hunique c e hec
    refine ⟨f,?_,?_,?_⟩
    · apply (G.eraseSource_iff v a hunique f).mpr
      rwa [hf]
    · apply G.eraseComponentMap_injective v a hunique
      rw [G.eraseComponentMap_edge,hf]
      exact hec
    · apply (G.eraseVertex_sourceFace_bounded_iff hc v a ha hunique f).mp
      rwa [hf]

theorem eraseComponentMap_ordinary_iff (hc : G.graph.Connected) (v a : Fin n)
    (ha : G.graph.Adj v a) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (c : TrackComponent (G.eraseVertex v)) :
    c∈(G.eraseVertex v).ordinaryTrackComponents ↔ G.eraseComponentMap v c∈G.ordinaryTrackComponents := by
  have h := G.eraseComponentMap_terminal_iff hc v a ha hunique c
  simpa only [(G.eraseVertex v).mem_terminalTrackComponents,G.mem_terminalTrackComponents,not_iff_not] using h

end PennyGraph
end Swanepoel
