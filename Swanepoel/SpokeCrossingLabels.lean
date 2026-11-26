module
public import Swanepoel.PentagonFirstCrossing
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PentagonFaceBoundary.boundary_spoke_component_injective {n : ℕ} {G : PennyGraph n}
    {F : PlaneFace G} (P : PentagonFaceBoundary G F) (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y) :
    Function.Injective (fun i : Fin 5 => edgeComponent (P.dart i)) := by
  have hport (i : Fin 5) : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  intro i j h
  have he := G.boundary_face_port_component_injective ht hY F hFY hports (hport i) (hport j) h
  exact P.vertex_injective (congrArg (fun e : OrientedEdge G => e.val.1) he)

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

theorem bank_difference_of_crossing (ht : G.TriangleFree) (i : Fin 5) (v : TrackComponent G)
    (hcross : ComponentCrosses (edgeComponent (P.dart i)) v) :
    (K.spine i).bankLabel (K.loop i) (-1)=(K.spine i).bankLabel (K.loop i) 1+1 := by
  have hport : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  obtain ⟨q,_,hprefix,_⟩ := crossing_cut_transition_before_source ht v (P.dart i)
    (Finset.mem_filter.mp hport).2.1 ((componentGraph G ht).ne_of_adj hcross) hcross
  obtain ⟨d,hsd,_⟩ := Relation.TransGen.head'_iff.mp (Relation.TransGen.tail' hprefix q.property)
  exact K.bank_difference_of_step i ⟨d,hsd⟩

theorem crossing_step_label_change (ht : G.TriangleFree) (i : Fin 5) (q : SpineTransition G)
    (hcut : cutRhombus (edgeComponent (P.dart i)) q.rhombus)
    (hne : edgeComponent q.val.1≠edgeComponent (P.dart i)) :
    (K.loop i).windingIndex (G.point q.val.2.val.1)=
        (K.loop i).windingIndex (G.point q.val.1.val.1)+1 ∨
      (K.loop i).windingIndex (G.point q.val.2.val.1)=
        (K.loop i).windingIndex (G.point q.val.1.val.1)-1 := by
  have hcross := cutRhombus_crosses_component ht q hne hcut
  have hdiff := K.bank_difference_of_crossing ht i _ ((componentGraph G ht).adj_symm hcross)
  obtain ⟨C,hE,hF,_⟩ := q.property
  have hAD := q.other_component_eq_cut ht _ hcut hne C hE hF
  have hrAD := (reverse_component C.edgeAD).symm.trans hAD
  have hsame : SameLine (carriedVector C.edgeAD) (carriedVector (P.dart i)) :=
    (component_sameLine C.edgeAD _ hAD).trans (component_sameLine (P.dart i) _ rfl).symm
  rcases hsame with hv | hv
  · have hstart := K.carried_start_bank_label ht i C.edgeAD hAD (-1) (Or.inr rfl)
      (by simpa only [neg_neg,one_smul] using hv)
    have hend := K.carried_start_bank_label ht i (reverseEdge C.edgeAD) hrAD 1 (Or.inl rfl)
      (by rw [reverseEdge_vector,hv,neg_one_smul])
    right
    simpa only [hE,hF,RhombusCell.edgeAD,reverseEdge] using
      (show (K.loop i).windingIndex (G.point C.d)=
          (K.loop i).windingIndex (G.point C.a)-1 by
        change (K.loop i).windingIndex (G.point C.a)=(K.spine i).bankLabel (K.loop i) (-1) at hstart
        change (K.loop i).windingIndex (G.point C.d)=(K.spine i).bankLabel (K.loop i) 1 at hend
        omega)
  · have hstart := K.carried_start_bank_label ht i C.edgeAD hAD 1 (Or.inl rfl)
      (by simpa only [neg_one_smul] using hv)
    have hend := K.carried_start_bank_label ht i (reverseEdge C.edgeAD) hrAD (-1) (Or.inr rfl)
      (by rw [reverseEdge_vector,hv]; simp only [neg_neg,one_smul])
    left
    simpa only [hE,hF,RhombusCell.edgeAD,reverseEdge] using
      (show (K.loop i).windingIndex (G.point C.d)=
          (K.loop i).windingIndex (G.point C.a)+1 by
        change (K.loop i).windingIndex (G.point C.a)=(K.spine i).bankLabel (K.loop i) 1 at hstart
        change (K.loop i).windingIndex (G.point C.d)=(K.spine i).bankLabel (K.loop i) (-1) at hend
        omega)

theorem crossing_step_other_label_eq (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (i : Fin 5) (q : SpineTransition G)
    (hcut : cutRhombus (edgeComponent (P.dart i)) q.rhombus)
    (hne : edgeComponent q.val.1≠edgeComponent (P.dart i))
    (j : Fin 5) (hji : j≠i) (hjnext : j+1≠i) :
    (K.loop j).windingIndex (G.point q.val.1.val.1)=
      (K.loop j).windingIndex (G.point q.val.2.val.1) := by
  obtain ⟨C,hE,hF,_⟩ := q.property
  have hAD := q.other_component_eq_cut ht _ hcut hne C hE hF
  have hinj := P.boundary_spoke_component_injective ht hY hFY hports
  have hnj : edgeComponent C.edgeAD≠edgeComponent (P.dart j) := by
    intro h
    exact hji (hinj (hAD.symm.trans h)).symm
  have hnnext : edgeComponent C.edgeAD≠edgeComponent (P.dart (j+1)) := by
    intro h
    exact hjnext (hinj (hAD.symm.trans h)).symm
  simpa only [hE,hF,RhombusCell.edgeAD] using
    (K.support j).edge_endpoint_winding_eq ht C.edgeAD hnj hnnext

end PentagonSpokeLoops
end Swanepoel
