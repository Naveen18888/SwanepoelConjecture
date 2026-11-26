module
public import Swanepoel.PentagonSectorCodes
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem unit_vector_ne_neg_self (v : Plane) (hv : ‖v‖=1) : v≠ -v := by
  intro h
  have hh := congrArg (fun x : Plane => inner ℝ v x) h
  rw [inner_neg_right,real_inner_self_eq_norm_sq,hv] at hh
  norm_num at hh

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

theorem carried_start_code_of_eq (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (j : Fin 5) (e : OrientedEdge G) (he : edgeComponent e=edgeComponent (P.dart j))
    (hv : carriedVector e=carriedVector (P.dart j)) : K.vertexCode e.val.1=K.rootCode j := by
  rcases K.carried_start_code ht hF j e he with h | h
  · exact h.2
  · exact False.elim (unit_vector_ne_neg_self _ (carriedVector_norm (P.dart j)) (hv.symm.trans h.1))

theorem carried_start_code_of_neg (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (j : Fin 5) (e : OrientedEdge G) (he : edgeComponent e=edgeComponent (P.dart j))
    (hv : carriedVector e= -carriedVector (P.dart j)) : K.vertexCode e.val.1=K.rootCode (j+1) := by
  rcases K.carried_start_code ht hF j e he with h | h
  · exact False.elim (unit_vector_ne_neg_self _ (carriedVector_norm (P.dart j)) (h.1.symm.trans hv))
  · exact h.2

theorem carried_edge_codes (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (j : Fin 5) (e : OrientedEdge G) (he : edgeComponent e=edgeComponent (P.dart j)) :
    (carriedVector e=carriedVector (P.dart j) ∧ K.vertexCode e.val.1=K.rootCode j ∧
      K.vertexCode e.val.2=K.rootCode (j+1)) ∨
    (carriedVector e= -carriedVector (P.dart j) ∧ K.vertexCode e.val.1=K.rootCode (j+1) ∧
      K.vertexCode e.val.2=K.rootCode j) := by
  have hr := (reverse_component e).symm.trans he
  rcases K.carried_start_code ht hF j e he with ⟨hv,hc⟩ | ⟨hv,hc⟩
  · left
    refine ⟨hv,hc,?_⟩
    exact K.carried_start_code_of_neg ht hF j (reverseEdge e) hr (by rw [reverseEdge_vector,hv])
  · right
    refine ⟨hv,hc,?_⟩
    exact K.carried_start_code_of_eq ht hF j (reverseEdge e) hr (by rw [reverseEdge_vector,hv,neg_neg])

theorem crossing_step_code_transition (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (i : Fin 5) (q : SpineTransition G)
    (hcut : cutRhombus (edgeComponent (P.dart i)) q.rhombus)
    (hne : edgeComponent q.val.1≠edgeComponent (P.dart i)) :
    (K.vertexCode q.val.1.val.1=K.rootCode i ∧ K.vertexCode q.val.2.val.1=K.rootCode (i+1) ∧
      inner ℝ (carriedVector (P.dart i)) (sourceNormal q.val.1)< -Real.sqrt 3/2) ∨
    (K.vertexCode q.val.1.val.1=K.rootCode (i+1) ∧ K.vertexCode q.val.2.val.1=K.rootCode i ∧
      Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart i)) (sourceNormal q.val.1)) := by
  have hcross := cutRhombus_crosses_component ht q hne hcut
  have habs := crossing_port_normal_abs_gt_sqrt_three_half ht (edgeComponent (P.dart i)) q.val.1
    ((componentGraph G ht).adj_symm hcross)
  rw [← (component_sameLine (P.dart i) _ rfl).abs_inner_eq (SameLine.refl (sourceNormal q.val.1))] at habs
  obtain ⟨C,hE,hF',hpositive⟩ := q.property
  have hAD := q.other_component_eq_cut ht _ hcut hne C hE hF'
  have hvector : carriedVector q.val.1=C.u := by simp only [carriedVector,hE,RhombusCell.u]
  have hdot : inner ℝ (carriedVector (P.dart i)) (sourceNormal q.val.1)=
      cross2 (carriedVector (P.dart i)) C.u := by rw [sourceNormal_inner_eq_cross,hvector]
  have hswap : cross2 C.v C.u= -cross2 C.u C.v := by unfold cross2; ring
  rcases K.carried_edge_codes ht hF i C.edgeAD hAD with ⟨hv,hstart,hend⟩ | ⟨hv,hstart,hend⟩
  · change C.v=carriedVector (P.dart i) at hv
    have hneg : inner ℝ (carriedVector (P.dart i)) (sourceNormal q.val.1)<0 := by
      rw [hdot,← hv,hswap]
      linarith only [hpositive]
    left
    refine ⟨?_,?_,?_⟩
    · simpa only [hE,RhombusCell.edgeAD] using hstart
    · simpa only [hF',RhombusCell.edgeAD] using hend
    · rw [abs_of_neg hneg] at habs
      linarith only [habs]
  · change C.v= -carriedVector (P.dart i) at hv
    have hneg : carriedVector (P.dart i)= -C.v := by rw [hv,neg_neg]
    have hpos : 0 < inner ℝ (carriedVector (P.dart i)) (sourceNormal q.val.1) := by
      rw [hdot,hneg,cross2_neg_left,hswap]
      linarith only [hpositive]
    right
    refine ⟨?_,?_,?_⟩
    · simpa only [hE,RhombusCell.edgeAD] using hstart
    · simpa only [hF',RhombusCell.edgeAD] using hend
    · rwa [abs_of_pos hpos] at habs

theorem uncut_step_code_eq (ht : G.TriangleFree) (q : SpineTransition G)
    (hcut : ∀ i : Fin 5,¬cutRhombus (edgeComponent (P.dart i)) q.rhombus) :
    K.vertexCode q.val.1.val.1=K.vertexCode q.val.2.val.1 := by
  obtain ⟨C,hE,hF,_⟩ := q.property
  have hside (i : Fin 5) : edgeComponent C.edgeAD≠edgeComponent (P.dart i) :=
    (show TrackCutStep (edgeComponent (P.dart i)) q.val.1 q.val.2 from ⟨q,rfl,hcut i⟩).other_component_ne ht C hE hF
  simpa only [hE,hF,RhombusCell.edgeAD] using K.nonspoke_edge_code_eq ht C.edgeAD hside

theorem defect_source_vertexCode (ht : G.TriangleFree) (e : OrientedEdge G)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F) :
    K.vertexCode e.val.1=K.code (G.sourceFace e) := by
  funext i
  exact (K.support i).defect_vertex_winding_label ht K.outer_unbounded _ heF heRoot _
    (G.sourceFace_endpoints_mem_closure e).1

theorem crossing_step_sector_transition (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (i : Fin 5) (q : SpineTransition G)
    (hcut : cutRhombus (edgeComponent (P.dart i)) q.rhombus)
    (hne : edgeComponent q.val.1≠edgeComponent (P.dart i)) :
    (K.vertexSector q.val.1.val.1=i ∧ K.vertexSector q.val.2.val.1=i+1 ∧
      inner ℝ (carriedVector (P.dart i)) (sourceNormal q.val.1)< -Real.sqrt 3/2) ∨
    (K.vertexSector q.val.1.val.1=i+1 ∧ K.vertexSector q.val.2.val.1=i ∧
      Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart i)) (sourceNormal q.val.1)) := by
  have ht' := K.crossing_step_code_transition ht (hY.subset_defects hFY) i q hcut hne
  rcases ht' with ⟨hs,ht',hdot⟩ | ⟨hs,ht',hdot⟩
  · left
    refine ⟨?_,?_,hdot⟩ <;> unfold vertexSector
    · rw [hs,K.codeSector_root ht hY hFY hports]
    · rw [ht',K.codeSector_root ht hY hFY hports]
  · right
    refine ⟨?_,?_,hdot⟩ <;> unfold vertexSector
    · rw [hs,K.codeSector_root ht hY hFY hports]
    · rw [ht',K.codeSector_root ht hY hFY hports]

end PentagonSpokeLoops
end Swanepoel
