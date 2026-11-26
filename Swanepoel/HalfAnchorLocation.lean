module
public import Swanepoel.HalfCutPiece
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable
namespace HalfCutPiece
variable {n : ℕ} {G : PennyGraph n} {cut v : TrackComponent G}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    (P : HalfCutPiece B ht side v)

theorem anchor_crossing_cell_codes (hcut : cut∈G.ordinaryTrackComponents)
    (hUV : ComponentCrosses cut v) (e : OrientedEdge G) (he : SpineSource e)
    (heY : G.sourceFace e∈B.bankDefectFamily ht side) (C : RhombusCell G)
    (hAB : edgeComponent C.edgeAB=edgeComponent e) (hAD : edgeComponent C.edgeAD=v) :
    ∀ i∈C.corners, decide (B.vertexLabel i=B.positiveLabel)=side := by
  have hCV : ComponentCrosses (edgeComponent e) v := ⟨C,Or.inl ⟨hAB,hAD⟩⟩
  have hmiss : ¬ComponentCrosses (edgeComponent e) cut := by
    intro hCU
    exact componentGraph_noTriple G ht cut v (edgeComponent e) hUV
      ((componentGraph G ht).adj_symm hCV) hCU
  have hnC := defect_source_component_ne_ordinary ht e he (Finset.mem_filter.mp heY).1 cut hcut
  have hnV : v≠cut := Ne.symm ((componentGraph G ht).ne_of_adj hUV)
  have hA := B.noncrossing_carried_piece_code ht side e C.edgeAB he heY hAB hnC hmiss
  change decide (B.vertexLabel C.a=B.positiveLabel)=side at hA
  have hABlab := G.noncut_edge_winding_equal ht cut B.outer B.loop B.support C.edgeAB
    (fun h => hnC (hAB.symm.trans h))
  have hADlab := G.noncut_edge_winding_equal ht cut B.outer B.loop B.support C.edgeAD
    (fun h => hnV (hAD.symm.trans h))
  have hDC : edgeComponent C.edgeDC=edgeComponent C.edgeAB := by
    apply Eq.symm
    exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inl ⟨C,rfl,rfl⟩))
  have hDClab := G.noncut_edge_winding_equal ht cut B.outer B.loop B.support C.edgeDC
    (fun h => hnC (hAB.symm.trans (hDC.symm.trans h)))
  change B.vertexLabel C.a=B.vertexLabel C.b at hABlab
  change B.vertexLabel C.a=B.vertexLabel C.d at hADlab
  change B.vertexLabel C.d=B.vertexLabel C.c at hDClab
  intro i hi
  simp only [RhombusCell.corners,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hA
  · rwa [← hABlab]
  · rwa [← hDClab,← hADlab]
  · rwa [← hADlab]

theorem anchor_crossing_midpoint_mem (hcut : cut∈G.ordinaryTrackComponents)
    (hUV : ComponentCrosses cut v) (e : OrientedEdge G) (he : SpineSource e)
    (heY : G.sourceFace e∈B.bankDefectFamily ht side) (C : RhombusCell G)
    (hAB : edgeComponent C.edgeAB=edgeComponent e) (hAD : edgeComponent C.edgeAD=v)
    (f : OrientedEdge G) (hf : edgeComponent f=v) (hfc : f.val.1∈C.corners) :
    edgeCenter f∈P.chain.positive.toPlane.trace := by
  apply P.midpoint_mem_of_code (Ne.symm ((componentGraph G ht).ne_of_adj hUV)) f hf
  exact anchor_crossing_cell_codes hcut hUV e he heY C hAB hAD f.val.1 hfc

theorem nontrivial_of_step_midpoints {e f : OrientedEdge G} (hef : PositiveCellStep e f)
    (he : edgeComponent e=v) (hem : edgeCenter e∈P.chain.positive.toPlane.trace)
    (hfm : edgeCenter f∈P.chain.positive.toPlane.trace) : P.start≠P.crossing.val.1 := by
  intro heq
  have hbE := P.chain.positive.height_bounds hem
  have hbF := P.chain.positive.height_bounds hfm
  rw [← heq] at hbE hbF
  have hh : cross2 (carriedVector P.start) (edgeCenter e)=
      cross2 (carriedVector P.start) (edgeCenter f) := by linarith
  have hv := generated_track_sameLine (Quotient.exact (he.trans P.component.symm))
  have hEF : edgeHeight e=edgeHeight f := by
    unfold edgeHeight
    rw [← hef.to_cellStep.vector_eq]
    rcases hv with hv | hv
    · rw [hv]
      exact hh
    · rw [hv,cross2_neg_left,cross2_neg_left,hh]
  exact (ne_of_lt hef.height_lt) hEF

end HalfCutPiece
end Swanepoel
