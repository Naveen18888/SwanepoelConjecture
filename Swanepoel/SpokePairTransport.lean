module
public import Swanepoel.PentagonSpokeLabels
public import Swanepoel.TwoSpineTransport
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

namespace PennyGraph.SpokePairSupport
variable {n : ℕ} {G : PennyGraph n} {c d : TrackComponent G} {F outer : PlaneFace G}
    {a : Plane} {loop : PlaneChain a a} (hloop : G.SpokePairSupport c d F outer loop)
include hloop

theorem edge_endpoint_winding_eq (ht : G.TriangleFree) (e : OrientedEdge G)
    (hec : edgeComponent e≠c) (hed : edgeComponent e≠d) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point e.val.2) := by
  have hpre : IsPreconnected (G.edgeTrace e.val.1 e.val.2) := by
    rw [G.edgeTrace_eq_segment]
    exact (convex_segment (𝕜 := ℝ) _ _).isPreconnected
  apply loop.windingIndex_constant hpre (hloop.edge_disjoint ht e hec hed)
  · exact ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
  · exact ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩

theorem masked_path_vertex_winding_eq (ht : G.TriangleFree) {e f : OrientedEdge G}
    (hpath : Relation.ReflTransGen (fun x y => TrackCutStep c x y ∧ TrackCutStep d x y) e f) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  induction hpath with
  | refl => rfl
  | @tail x y hx hxy ih =>
    obtain ⟨C,hX,hY,_⟩ := hxy.1.to_positive
    have hh := hloop.edge_endpoint_winding_eq ht C.edgeAD
      (hxy.1.other_component_ne ht C hX hY) (hxy.2.other_component_ne ht C hX hY)
    exact ih.trans (by simpa only [hX,hY,RhombusCell.edgeAD] using hh)

theorem masked_path_missing_other_winding_eq (ht : G.TriangleFree) {e f : OrientedEdge G}
    (hpath : Relation.ReflTransGen (TrackCutStep c) e f)
    (hne : edgeComponent e≠d) (hmiss : ¬ComponentCrosses (edgeComponent e) d) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  induction hpath with
  | refl => rfl
  | @tail x y hx hxy ih =>
    have hpos := Relation.ReflTransGen.mono (fun _ _ h => h.to_positive) _ _ hx
    have hc := (positive_path_component hpos).symm
    have hd := noncrossing_step_preserved ht (hc ▸ hne) (hc ▸ hmiss) hxy.to_positive
    have hh := hloop.masked_path_vertex_winding_eq ht
      (Relation.ReflTransGen.single ⟨hxy,hd⟩)
    exact ih.trans hh

end PennyGraph.SpokePairSupport

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

theorem carried_start_bank_label (ht : G.TriangleFree) (i : Fin 5) (e : OrientedEdge G)
    (he : edgeComponent e=edgeComponent (P.dart i)) (sign : ℝ) (hsign : sign=1 ∨ sign= -1)
    (hv : carriedVector e=(-sign) • carriedVector (P.dart i)) :
    (K.loop i).windingIndex (G.point e.val.1)=(K.spine i).bankLabel (K.loop i) sign := by
  have hs : SpineSource (P.dart i) := by
    have hm : P.dart i∈G.faceSourcePorts F := by
      rw [← P.darts]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    exact (Finset.mem_filter.mp hm).2.1
  apply (K.spine i).carried_start_label_of_mem (K.loop i) sign (K.bank_disjoint i sign hsign) e ?_ hv
  rw [(K.spine i).complete_trace ht hs (K.sink i)]
  exact Or.inl ⟨e,he,rfl⟩

theorem crossing_source_label_of_missing_next (ht : G.TriangleFree) (i : Fin 5)
    (e : OrientedEdge G) (he : SpineSource e)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F)
    (hcross : ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i)))
    (hneNext : edgeComponent e≠edgeComponent (P.dart (i+1)))
    (hmiss : ¬ComponentCrosses (edgeComponent e) (edgeComponent (P.dart (i+1)))) :
    (0 < inner ℝ (carriedVector (P.dart i)) (sourceNormal e) ∧
      K.code (G.sourceFace e) i=(K.spine i).bankLabel (K.loop i) 1) ∨
    (inner ℝ (carriedVector (P.dart i)) (sourceNormal e)<0 ∧
      K.code (G.sourceFace e) i=(K.spine i).bankLabel (K.loop i) (-1)) := by
  have hne := (componentGraph G ht).ne_of_adj hcross
  obtain ⟨q,hqcut,hprefix,hpairs⟩ := crossing_cut_transition_before_source ht
    (edgeComponent (P.dart i)) e he hne hcross
  have hpath := path_before_global_cut_preserved (edgeComponent (P.dart i)) q hpairs hprefix
  have hlabels := (K.support i).masked_path_missing_other_winding_eq ht hpath hneNext hmiss
  obtain ⟨C,hE,hF,hpos⟩ := q.property
  have hqne : edgeComponent q.val.1≠edgeComponent (P.dart i) := by
    rwa [← positive_path_component hprefix]
  have hAD := q.other_component_eq_cut ht _ hqcut hqne C hE hF
  have hvector : carriedVector e=C.u := by
    rw [positive_path_vector_eq hprefix]
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
    · rw [hdot,← hv,hswap]; linarith only [hpos]
    · rw [hface]
      exact K.carried_start_bank_label ht i C.edgeAD hAD (-1) (Or.inr rfl)
        (by simpa only [neg_neg,one_smul,carriedVector,RhombusCell.edgeAD,RhombusCell.v] using hv)
  · change C.v= -carriedVector (P.dart i) at hv
    have hneg : carriedVector (P.dart i)= -C.v := by rw [hv,neg_neg]
    left
    refine ⟨?_,?_⟩
    · rw [hdot,hneg,cross2_neg_left,hswap]; linarith only [hpos]
    · rw [hface]
      exact K.carried_start_bank_label ht i C.edgeAD hAD 1 (Or.inl rfl)
        (by simpa only [neg_one_smul,carriedVector,RhombusCell.edgeAD,RhombusCell.v] using hv)

theorem crossing_join_code_ne_of_missing_next (ht : G.TriangleFree) (i : Fin 5)
    (e f : OrientedEdge G) (he : SpineSource e) (hf : SpineSource f)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (hfF : G.sourceFace f∈G.defectPlaneFaces ht)
    (heRoot : G.sourceFace e≠F) (hfRoot : G.sourceFace f≠F)
    (hc : edgeComponent f=edgeComponent e) (hne : f≠e)
    (hcross : ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i)))
    (hneNext : edgeComponent e≠edgeComponent (P.dart (i+1)))
    (hmiss : ¬ComponentCrosses (edgeComponent e) (edgeComponent (P.dart (i+1)))) :
    K.code (G.sourceFace e)≠K.code (G.sourceFace f) := by
  have hn := source_normals_opposite ht he hf hc hne
  have hb := K.bank_labels_distinct_of_crossing ht i _ ((componentGraph G ht).adj_symm hcross)
  have hE := K.crossing_source_label_of_missing_next ht i e he heF heRoot hcross hneNext hmiss
  have hF := K.crossing_source_label_of_missing_next ht i f hf hfF hfRoot
    (hc ▸ hcross) (hc ▸ hneNext) (hc ▸ hmiss)
  intro hcode
  have hcoord := congrFun hcode i
  rcases hE with ⟨hp,hpL⟩ | ⟨hp,hpL⟩ <;> rcases hF with ⟨hq,hqL⟩ | ⟨hq,hqL⟩
  · rw [hn,inner_neg_right] at hq
    linarith only [hp,hq]
  · exact hb (hpL.symm.trans (hcoord.trans hqL))
  · exact hb (hqL.symm.trans (hcoord.symm.trans hpL))
  · rw [hn,inner_neg_right] at hq
    linarith only [hp,hq]

end PentagonSpokeLoops
end Swanepoel
