module
public import Swanepoel.SpokePairTransport
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem first_mask_failure {α : Type*} {R M : α→α→Prop} {e f g : α}
    (hpath : Relation.ReflTransGen R e f) (hstep : R f g) (hfail : ¬M f g) :
    ∃ a b,R a b ∧ ¬M a b ∧ Relation.ReflTransGen M e a := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨f,g,hstep,hfail,Relation.ReflTransGen.refl⟩
  | @head a b hab hbf ih =>
    by_cases hm : M a b
    · obtain ⟨x,y,hxy,hnot,hprefix⟩ := ih
      exact ⟨x,y,hxy,hnot,hprefix.head hm⟩
    · exact ⟨a,b,hab,hm,Relation.ReflTransGen.refl⟩

theorem PennyGraph.first_pentagon_spoke_hit {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (P : PentagonFaceBoundary G F)
    (e : OrientedEdge G) (he : SpineSource e)
    (hcross : ∃ i : Fin 5,ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i))) :
    ∃ (i : Fin 5) (q : SpineTransition G),cutRhombus (edgeComponent (P.dart i)) q.rhombus ∧
      Relation.ReflTransGen (fun x y => ∀ j : Fin 5,TrackCutStep (edgeComponent (P.dart j)) x y) e q.val.1 := by
  obtain ⟨i,hi⟩ := hcross
  have hne := (componentGraph G ht).ne_of_adj hi
  obtain ⟨q,hcut,hprefix,_⟩ := crossing_cut_transition_before_source ht _ e he hne hi
  let M (x y : OrientedEdge G) := ∀ j : Fin 5,TrackCutStep (edgeComponent (P.dart j)) x y
  have hfail : ¬M q.val.1 q.val.2 := by
    intro hm
    obtain ⟨p,hp,hnot⟩ := hm i
    have heq : p=q := Subtype.ext hp
    exact hnot (heq ▸ hcut)
  obtain ⟨a,b,hab,hnot,hpath⟩ := first_mask_failure hprefix q.property hfail
  have hnot' : ¬∀ j : Fin 5,TrackCutStep (edgeComponent (P.dart j)) a b := hnot
  push Not at hnot'
  obtain ⟨j,hj⟩ := hnot'
  let r : SpineTransition G := ⟨(a,b),hab⟩
  refine ⟨j,r,?_,hpath⟩
  by_contra hn
  exact hj ⟨r,rfl,hn⟩

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

theorem crossing_source_label_of_masked_prefix (ht : G.TriangleFree) (i : Fin 5)
    (e : OrientedEdge G) (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F)
    (q : SpineTransition G) (hqcut : cutRhombus (edgeComponent (P.dart i)) q.rhombus)
    (hprefix : Relation.ReflTransGen
      (fun x y => TrackCutStep (edgeComponent (P.dart i)) x y ∧
        TrackCutStep (edgeComponent (P.dart (i+1))) x y) e q.val.1)
    (hne : edgeComponent e≠edgeComponent (P.dart i)) :
    (0 < inner ℝ (carriedVector (P.dart i)) (sourceNormal e) ∧
      K.code (G.sourceFace e) i=(K.spine i).bankLabel (K.loop i) 1) ∨
    (inner ℝ (carriedVector (P.dart i)) (sourceNormal e)<0 ∧
      K.code (G.sourceFace e) i=(K.spine i).bankLabel (K.loop i) (-1)) := by
  have hpos := Relation.ReflTransGen.mono (fun _ _ h => h.1.to_positive) _ _ hprefix
  have hlabels := (K.support i).masked_path_vertex_winding_eq ht hprefix
  obtain ⟨C,hE,hF,hpositive⟩ := q.property
  have hqne : edgeComponent q.val.1≠edgeComponent (P.dart i) := by
    rwa [← positive_path_component hpos]
  have hAD := q.other_component_eq_cut ht _ hqcut hqne C hE hF
  have hvector : carriedVector e=C.u := by
    rw [positive_path_vector_eq hpos]
    simp only [carriedVector,hE,RhombusCell.u]
  have hdot : inner ℝ (carriedVector (P.dart i)) (sourceNormal e)=
      cross2 (carriedVector (P.dart i)) C.u := by rw [sourceNormal_inner_eq_cross,hvector]
  have hswap : cross2 C.v C.u= -cross2 C.u C.v := by unfold cross2; ring
  have hface : K.code (G.sourceFace e) i=(K.loop i).windingIndex (G.point C.a) := by
    rw [code,← (K.support i).defect_vertex_winding_label ht K.outer_unbounded
      _ heF heRoot _ (G.sourceFace_endpoints_mem_closure e).1]
    simpa only [hE] using hlabels
  have hsame : SameLine (carriedVector C.edgeAD) (carriedVector (P.dart i)) :=
    (component_sameLine C.edgeAD _ hAD).trans (component_sameLine (P.dart i) _ rfl).symm
  rcases hsame with hv | hv
  · change C.v=carriedVector (P.dart i) at hv
    right
    refine ⟨?_,?_⟩
    · rw [hdot,← hv,hswap]; linarith only [hpositive]
    · rw [hface]
      exact K.carried_start_bank_label ht i C.edgeAD hAD (-1) (Or.inr rfl)
        (by simpa only [neg_neg,one_smul,carriedVector,RhombusCell.edgeAD,RhombusCell.v] using hv)
  · change C.v= -carriedVector (P.dart i) at hv
    have hneg : carriedVector (P.dart i)= -C.v := by rw [hv,neg_neg]
    left
    refine ⟨?_,?_⟩
    · rw [hdot,hneg,cross2_neg_left,hswap]; linarith only [hpositive]
    · rw [hface]
      exact K.carried_start_bank_label ht i C.edgeAD hAD 1 (Or.inl rfl)
        (by simpa only [neg_one_smul,carriedVector,RhombusCell.edgeAD,RhombusCell.v] using hv)

theorem exists_first_crossing_sharp_bank_label (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (e : OrientedEdge G) (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F)
    (hcross : ∃ i : Fin 5,ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i))) :
    ∃ i : Fin 5,
      (Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart i)) (sourceNormal e) ∧
        K.code (G.sourceFace e) i=(K.spine i).bankLabel (K.loop i) 1) ∨
      (inner ℝ (carriedVector (P.dart i)) (sourceNormal e)< -Real.sqrt 3/2 ∧
        K.code (G.sourceFace e) i=(K.spine i).bankLabel (K.loop i) (-1)) := by
  obtain ⟨i,q,hcut,hprefix⟩ := G.first_pentagon_spoke_hit ht F P e
    (G.spineSource_of_sourceFace_mem_defects ht e heF) hcross
  have hport : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hne := G.boundary_face_other_defect_component_ne ht hY F hFY hports
    (P.dart i) e hport heF heRoot
  have hpos := Relation.ReflTransGen.mono (fun _ _ h => (h i).to_positive) _ _ hprefix
  have hcomp := positive_path_component hpos
  have hqne : edgeComponent q.val.1≠edgeComponent (P.dart i) := by rwa [← hcomp]
  have hcrossE : ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i)) := by
    rw [hcomp]
    exact cutRhombus_crosses_component ht q hqne hcut
  have habs := crossing_port_normal_abs_gt_sqrt_three_half ht (edgeComponent (P.dart i)) e
    ((componentGraph G ht).adj_symm hcrossE)
  rw [← (component_sameLine (P.dart i) _ rfl).abs_inner_eq (SameLine.refl (sourceNormal e))] at habs
  have hlabel := K.crossing_source_label_of_masked_prefix ht i e heF heRoot q hcut
    (Relation.ReflTransGen.mono (fun _ _ h => ⟨h i,h (i+1)⟩) _ _ hprefix) hne
  refine ⟨i,?_⟩
  rcases hlabel with ⟨hp,hl⟩ | ⟨hn,hl⟩
  · exact Or.inl ⟨by simpa only [abs_of_pos hp] using habs,hl⟩
  · exact Or.inr ⟨by rw [abs_of_neg hn] at habs; linarith only [habs],hl⟩

end PentagonSpokeLoops
end Swanepoel
