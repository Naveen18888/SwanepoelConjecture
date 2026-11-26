module
public import Swanepoel.SpineSectorWalks
public import Swanepoel.PentagonConeAccounting
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PositiveSpineChain
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem mem_crossedSpokes_of_prefix_step {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (ht : G.TriangleFree) (htop : ¬∃g,PositiveCellStep t g) (i : Fin 5) (q : SpineTransition G)
    (hprefix : Relation.ReflTransGen PositiveCellStep s q.val.1)
    (hcut : cutRhombus (edgeComponent (P.dart i)) q.rhombus) : i∈p.crossedSpokes P := by
  induction p generalizing q with
  | nil s =>
    rcases hprefix.cases_head with h | ⟨d,hsd,_⟩
    · exact False.elim (htop ⟨q.val.2,by rw [h]; exact q.property⟩)
    · exact False.elim (htop ⟨d,hsd⟩)
  | cons s d t h tail ih =>
    by_cases hqs : q.val.1=s
    · have hqd : q.val.2=d := positive_step_functional ht (by simpa only [hqs] using q.property) h
      have hq : q=(⟨(s,d),h⟩ : SpineTransition G) := Subtype.ext (Prod.ext hqs hqd)
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [← hq]⟩
    · have hde : Relation.ReflTransGen PositiveCellStep d q.val.1 := by
        rcases hprefix.cases_head with hh | ⟨g,hsg,hgq⟩
        · exact False.elim (hqs hh.symm)
        · have hgd := positive_step_functional ht hsg h
          simpa only [hgd] using hgq
      exact Finset.mem_union_right _ (ih htop q hde hcut)

theorem crossing_mem_crossedSpokes {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (ht : G.TriangleFree) (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (i : Fin 5) (hcross : ComponentCrosses (edgeComponent s) (edgeComponent (P.dart i))) :
    i∈p.crossedSpokes P := by
  have hne := (componentGraph G ht).ne_of_adj hcross
  obtain ⟨q,hcut,hprefix,_⟩ := crossing_cut_transition_before_source ht _ s hs hne hcross
  exact p.mem_crossedSpokes_of_prefix_step P ht htop i q hprefix hcut

theorem pentagon_crossing_degree_le_hitCount {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (ht : G.TriangleFree) (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y)
    (hne : ∀ i : Fin 5,edgeComponent s≠edgeComponent (P.dart i)) :
    G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent s)≤p.pentagonHitCount P := by
  have hinj := P.boundary_spoke_component_injective ht hY hFY hports
  have htracks : G.familyTrackComponents {F}=Finset.univ.image (fun i : Fin 5 => edgeComponent (P.dart i)) := by
    rw [PennyGraph.familyTrackComponents,G.familySourcePorts_singleton,← P.darts,Finset.image_image]
    rfl
  unfold PennyGraph.familyCrossingDegree
  rw [htracks,Finset.filter_image,Finset.card_image_of_injective _ hinj]
  have hsub : (Finset.univ.filter (fun i : Fin 5 =>
      ComponentCrosses (edgeComponent (P.dart i)) (edgeComponent s)))⊆p.crossedSpokes P := by
    intro i hi
    exact p.crossing_mem_crossedSpokes P ht hs htop i
      ((componentGraph G ht).adj_symm (Finset.mem_filter.mp hi).2)
  exact (Finset.card_le_card hsub).trans (p.crossedSpokes_card_le_hitCount P ht hY hFY hports hne)

end PositiveSpineChain

theorem PennyGraph.isolated_pentagon_crossing_degree_le_two {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (P : PentagonFaceBoundary G F) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (e : OrientedEdge G) (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F) :
    G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)≤2 := by
  obtain ⟨K⟩ := P.exists_spoke_loops ht hY hFY hports
  have he := G.spineSource_of_sourceFace_mem_defects ht e heF
  obtain ⟨t,hreach,htop⟩ := exists_spine_end e
  obtain ⟨p⟩ := PositiveSpineChain.exists_of_reach hreach
  have hport (i : Fin 5) : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hne (i : Fin 5) : edgeComponent e≠edgeComponent (P.dart i) :=
    G.boundary_face_other_defect_component_ne ht hY F hFY hports (P.dart i) e (hport i) heF heRoot
  exact (p.pentagon_crossing_degree_le_hitCount P ht he htop hY hFY hports hne).trans
    (p.pentagonHitCount_le_two P K ht hY hFY hports hne)

theorem PennyGraph.isolated_five_port_crossing_degree_le_two {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (F : PlaneFace G) (hFY : F∈Y)
    (hfive : (G.faceSourcePorts F).card=5)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (e : OrientedEdge G) (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F) :
    G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)≤2 := by
  obtain ⟨P⟩ := G.five_port_face_boundary ht F (hY.subset_defects hFY) hdegree hfive
  exact G.isolated_pentagon_crossing_degree_le_two ht hY F P hFY hports e heF heRoot

end Swanepoel
