module
public import Swanepoel.L38HalfAreaFamilies
public import Swanepoel.L38HalfExterior
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bounded_half_face_original (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) (K : PlaneFace (B.halfGraph side))
    (hb : Bornology.IsBounded K.val) : G.IsFace K.val :=
  G.boundedFace_original_of_deleted_components_unbounded (B.halfGraph side)
    (B.halfGraph_drawing_subset side) (B.deleted_drawing_component_unbounded ht hc hcut side)
    ⟨K.val,K.property,hb⟩

theorem bounded_half_face_vertex_mem (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) (K : PlaneFace (B.halfGraph side))
    (hb : Bornology.IsBounded K.val) (v : Fin n) (hv : G.point v∈closure K.val) :
    v∈B.bankVertices side := by
  have hG := B.bounded_half_face_original ht hc hcut side K hb
  by_contra hnot
  have hfront : G.point v∈frontier K.val := by
    rw [frontier,K.property.isOpen.interior_eq]
    refine ⟨hv,?_⟩
    intro hz
    exact G.face_subset_complement ⟨K.val,hG⟩ hz (G.point_mem_drawing v)
  exact B.point_not_mem_halfGraph side v hnot
    ((B.halfGraph side).face_frontier_subset_drawing K hfront)

theorem bounded_half_source_is_old (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) (he : SpineSource e)
    (hb : Bornology.IsBounded ((B.halfGraph side).sourceFace e).val) :
    SpineSource (B.halfEdge side e) := by
  let K := (B.halfGraph side).sourceFace e
  have hG := B.bounded_half_face_original ht hc hcut side K hb
  have hsub := G.sourceFace_subset_of_drawing_subset (B.halfGraph side) (B.halfGraph_drawing_subset side)
    (B.halfEdge side e) e (B.halfEdge_vector side e).symm rfl
  have hOld : (G.sourceFace (B.halfEdge side e)).val=K.val := by
    have hz := G.sourceProbe_mem_sourceFace (B.halfEdge side e)
    exact ((G.sourceFace (B.halfEdge side e)).property.eq_component hz).trans
      (hG.eq_component (hsub hz)).symm
  rintro ⟨f,hfe⟩
  obtain ⟨C,hf,heC,hpos⟩ := hfe
  have hface := G.sourceFace_eq_positive_predecessor_cell ht (B.halfEdge side e) C heC hpos
  have hfA : G.point f.val.1∈closure K.val := by
    rw [← hOld,hface,C.closure_openRegion_eq ht]
    rw [hf]
    exact (C.boundary_coordinates ht (C.point_corner_mem_boundary C.a (by simp [RhombusCell.corners]))).1
  have hfB : G.point f.val.2∈closure K.val := by
    rw [← hOld,hface,C.closure_openRegion_eq ht]
    rw [hf]
    exact (C.boundary_coordinates ht (C.point_corner_mem_boundary C.b (by simp [RhombusCell.corners]))).1
  have ha := B.bounded_half_face_vertex_mem ht hc hcut side K hb f.val.1 hfA
  have hb' := B.bounded_half_face_vertex_mem ht hc hcut side K hb f.val.2 hfB
  let fH := B.liftHalfEdge side f ha hb'
  let E : L38HalfPentagonEmbedding (B.halfGraph side) G :=
    ⟨B.halfVertex side,B.halfVertex_injective side,B.halfGraph_point side⟩
  apply he
  refine ⟨fH,(E.positive_step_iff fH e).mpr ?_⟩
  change PositiveCellStep (B.halfEdge side fH) (B.halfEdge side e)
  rw [B.halfEdge_lift side f ha hb']
  exact ⟨C,hf,heC,hpos⟩

theorem half_defect_bank_face_surjective (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    ∀ K∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side),
      ∃ F : PlaneFace G,∃ hF : F∈B.bankDefectFamily ht side,B.bankDefectPlaneFace ht side F hF=K := by
  intro K hK
  have hKbounded := (B.halfGraph side).defectPlaneFace_isBounded (B.halfGraph_triangleFree ht side) hK
  have hfive := (B.halfGraph side).defect_source_ports_five_le (B.halfGraph_triangleFree ht side) K hK
  have hpos : 0<((B.halfGraph side).faceSourcePorts K).card := by omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
  have hep := (Finset.mem_filter.mp he).2
  have heBounded : Bornology.IsBounded ((B.halfGraph side).sourceFace e).val := hep.2 ▸ hKbounded
  have heOld := B.bounded_half_source_is_old ht hc hcut side e hep.1 heBounded
  have hG := B.bounded_half_face_original ht hc hcut side K hKbounded
  have hsub := G.sourceFace_subset_of_drawing_subset (B.halfGraph side) (B.halfGraph_drawing_subset side)
    (B.halfEdge side e) e (B.halfEdge_vector side e).symm rfl
  rw [hep.2] at hsub
  have hOld : (G.sourceFace (B.halfEdge side e)).val=K.val := by
    have hz := G.sourceProbe_mem_sourceFace (B.halfEdge side e)
    exact ((G.sourceFace (B.halfEdge side e)).property.eq_component hz).trans
      (hG.eq_component (hsub hz)).symm
  have hOldDef : G.sourceFace (B.halfEdge side e)∈G.defectPlaneFaces ht := by
    rcases G.sourceFace_defect_or_unbounded ht (B.halfEdge side e) heOld with hd | ho
    · exact hd
    · exact False.elim (ho (hOld.symm ▸ hKbounded))
  have hOldBank : G.sourceFace (B.halfEdge side e)∈B.bankDefectFamily ht side := by
    refine Finset.mem_filter.mpr ⟨hOldDef,?_⟩
    have hlabel := B.defect_source_vertex_label ht (B.halfEdge side e) hOldDef
    change decide (B.faceLabel (G.sourceFace (B.halfEdge side e))=B.positiveLabel)=side
    rw [← hlabel]
    exact (B.mem_bankVertices side _).mp (B.halfVertex_mem side e.val.1)
  refine ⟨G.sourceFace (B.halfEdge side e),hOldBank,?_⟩
  exact Subtype.ext hOld

theorem half_defect_area_lower (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a) :
    (B.halfGraph side).DefectAreaLowerBound (B.halfGraph_triangleFree ht side) :=
  B.half_defect_area_lower_of_bank_face_surjective ht side hdegree
    (B.half_defect_bank_face_surjective ht hc hcut side)

theorem bankDefectImage_all (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    B.bankDefectImage ht side (B.bankDefectFamily ht side) (Finset.Subset.refl _)=
      (B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side) := by
  apply Finset.Subset.antisymm
  · exact B.bankDefectImage_subset_defects ht side _ _
  · intro K hK
    obtain ⟨F,hF,rfl⟩ := B.half_defect_bank_face_surjective ht hc hcut side K hK
    exact B.bankDefectImage_mem ht side _ (Finset.Subset.refl _) F hF

end OrdinaryCutBanks
end Swanepoel
