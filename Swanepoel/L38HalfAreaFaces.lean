module
public import Swanepoel.FacePortIncidence
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PennyGraph.isFace_of_drawing_subset_of_frontier_retained {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (hHG : H.drawing⊆G.drawing)
    (F : PlaneFace G) (hfront : frontier F.val⊆H.drawing) : H.IsFace F.val := by
  obtain ⟨x,hx⟩ := F.property.nonempty
  have hFcompl : F.val⊆H.drawingᶜ := by
    intro z hz hdraw
    exact G.face_subset_complement F hz (hHG hdraw)
  have hxcompl := hFcompl hx
  let C := connectedComponentIn H.drawingᶜ x
  have hFC : F.val⊆C := (G.face_preconnected F).subset_connectedComponentIn hx hFcompl
  have hCF : C⊆F.val := by
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset F.property.isOpen
      ⟨x,mem_connectedComponentIn hxcompl,hx⟩
    intro z hz
    by_contra hzF
    have hzfront : z∈frontier F.val := by
      rw [frontier,F.property.isOpen.interior_eq]
      exact ⟨hz.1,hzF⟩
    exact (connectedComponentIn_subset _ _ hz.2) (hfront hzfront)
  exact ⟨x,hxcompl,Set.Subset.antisymm hFC hCF⟩

def PennyGraph.retainedPlaneFace {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing⊆G.drawing) (F : PlaneFace G)
    (hfront : frontier F.val⊆H.drawing) : PlaneFace H :=
  ⟨F.val,G.isFace_of_drawing_subset_of_frontier_retained H hHG F hfront⟩

theorem PennyGraph.retainedPlaneFace_val {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing⊆G.drawing) (F : PlaneFace G)
    (hfront : frontier F.val⊆H.drawing) :
    (G.retainedPlaneFace H hHG F hfront).val=F.val := rfl

theorem PennyGraph.sourceFace_subset_of_drawing_subset {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (hHG : H.drawing⊆G.drawing)
    (e : OrientedEdge G) (f : OrientedEdge H)
    (hvector : carriedVector f=carriedVector e)
    (hmid : H.edgePoint f.val.1 f.val.2 (1/2)=G.edgePoint e.val.1 e.val.2 (1/2)) :
    (G.sourceFace e).val⊆(H.sourceFace f).val := by
  let dG := G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2)
  let dH := H.edgeClearance (H.sourceProbeDrawing f) (physicalEdge f) (1/2)
  let d := min dG dH
  let p := G.edgePoint e.val.1 e.val.2 (1/2)
  let z := p+(-d) • quarterTurn (carriedVector e)
  have hd : 0<d := lt_min (G.sourceProbe_offset_pos e) (H.sourceProbe_offset_pos f)
  have hr := (normal_offset_mem_halfBalls (carriedVector e) p (carriedVector_norm e) hd).2
  have hrG : z∈rightHalfBall (carriedVector e) p (2*dG) :=
    ⟨Metric.ball_subset_ball (by dsimp [d]; linarith [min_le_left dG dH]) hr.1,hr.2⟩
  have hrH : z∈rightHalfBall (carriedVector f) (H.edgePoint f.val.1 f.val.2 (1/2)) (2*dH) := by
    rw [hvector,hmid]
    exact ⟨Metric.ball_subset_ball (by dsimp [d]; linarith [min_le_right dG dH]) hr.1,hr.2⟩
  have hzG : z∈(G.sourceFace e).val := G.right_halfBall_subset_sourceFace e hrG
  have hzH : z∈(H.sourceFace f).val := H.right_halfBall_subset_sourceFace f hrH
  have hcomp : (G.sourceFace e).val⊆H.drawingᶜ := by
    intro q hq hdraw
    exact G.face_subset_complement (G.sourceFace e) hq (hHG hdraw)
  have hs := (G.face_preconnected (G.sourceFace e)).subset_connectedComponentIn hzG hcomp
  rwa [← (H.sourceFace f).property.eq_component hzH] at hs

theorem PennyGraph.sourceFace_eq_of_retained_face {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (hHG : H.drawing⊆G.drawing)
    (e : OrientedEdge G) (f : OrientedEdge H)
    (hvector : carriedVector f=carriedVector e)
    (hmid : H.edgePoint f.val.1 f.val.2 (1/2)=G.edgePoint e.val.1 e.val.2 (1/2))
    (hface : H.IsFace (G.sourceFace e).val) :
    (H.sourceFace f).val=(G.sourceFace e).val := by
  have hs := G.sourceFace_subset_of_drawing_subset H hHG e f hvector hmid
  obtain ⟨z,hz⟩ := (G.sourceFace e).property.nonempty
  exact ((H.sourceFace f).property.eq_component (hs hz)).trans (hface.eq_component hz).symm

theorem PennyGraph.boundedFace_original_of_deleted_components_unbounded {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (hHG : H.drawing⊆G.drawing)
    (hescape : ∀ z∈G.drawing,z∉H.drawing →
      ¬Bornology.IsBounded (connectedComponentIn H.drawingᶜ z))
    (F : BoundedFace H) : G.IsFace F.val := by
  have hFcomplH : F.val⊆H.drawingᶜ := H.face_subset_complement ⟨F.val,F.property.1⟩
  have hFcomplG : F.val⊆G.drawingᶜ := by
    intro z hz hzG
    have hsame := F.property.1.eq_component hz
    exact hescape z hzG (hFcomplH hz) (hsame ▸ F.property.2)
  obtain ⟨x,hx⟩ := F.property.1.nonempty
  have hFG : F.val⊆connectedComponentIn G.drawingᶜ x :=
    (H.face_preconnected ⟨F.val,F.property.1⟩).subset_connectedComponentIn hx hFcomplG
  have hGF : connectedComponentIn G.drawingᶜ x⊆F.val := by
    rw [F.property.1.eq_component hx]
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (hFcomplG hx))
    intro z hz hzH
    exact (connectedComponentIn_subset _ _ hz) (hHG hzH)
  exact ⟨x,hFcomplG hx,Set.Subset.antisymm hFG hGF⟩

theorem PennyGraph.face_frontier_retained_of_vertices_and_edges {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (F : PlaneFace G)
    (hvertex : ∀ v : Fin n,G.point v∈closure F.val → G.point v∈H.drawing)
    (hedge : ∀ e : OrientedEdge G,G.sourceFace e=F →
      G.edgeTrace e.val.1 e.val.2⊆H.drawing) : frontier F.val⊆H.drawing := by
  intro z hz
  have hzdraw : z∈G.subdrawing Finset.univ := by
    rw [G.subdrawing_univ]
    exact G.face_frontier_subset_drawing F hz
  rcases hzdraw with ⟨v,rfl⟩ | hzedge
  · exact hvertex v hz.1
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp hzedge
    obtain ⟨_,t,ht,hparam⟩ := Set.mem_iUnion.mp he
    by_cases ht0 : t=0
    · have hpoint : G.point e.val.1=z := by
        simpa only [PennyGraph.edgePoint,ht0,sub_zero,one_smul,zero_smul,add_zero] using hparam
      exact hpoint ▸ hvertex e.val.1 (hpoint.symm ▸ hz.1)
    by_cases ht1 : t=1
    · have hpoint : G.point e.val.2=z := by
        simpa only [PennyGraph.edgePoint,ht1,sub_self,zero_smul,one_smul,zero_add] using hparam
      exact hpoint ▸ hvertex e.val.2 (hpoint.symm ▸ hz.1)
    have ht0' : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have ht1' : t<1 := lt_of_le_of_ne ht.2 ht1
    have hcl : G.edgePoint e.val.1 e.val.2 t∈closure F.val := hparam.symm ▸ hz.1
    rcases G.face_incident_to_open_edge F e ht0' ht1' hcl with hright | hleft
    · exact hedge e.forwardEdge hright ⟨t,ht,hparam⟩
    · apply hedge (reverseEdge e.forwardEdge) hleft
      change z∈G.edgeTrace e.val.2 e.val.1
      rw [← G.edgeTrace_reverse]
      exact ⟨t,ht,hparam⟩
end Swanepoel
