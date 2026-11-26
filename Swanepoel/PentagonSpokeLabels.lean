module
public import Swanepoel.BoundarySpokeBanks
public import Swanepoel.PentagonConeCount
public import Swanepoel.CrossingSourceBanks
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.boundary_face_port_component_injective {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y) :
    Set.InjOn edgeComponent (G.faceSourcePorts F : Set (OrientedEdge G)) := by
  intro e he f hf hc
  have heY : e∈G.familySourcePorts Y := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2.1,(Finset.mem_filter.mp he).2.2 ▸ hFY⟩
  have hfY : f∈G.familySourcePorts Y := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Finset.mem_filter.mp hf).2.1,(Finset.mem_filter.mp hf).2.2 ▸ hFY⟩
  exact G.bounded_sources_eq_on_boundary_track ht hY heY hfY hc (hports e he)

theorem PennyGraph.boundary_face_other_defect_component_ne {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (s e : OrientedEdge G) (hs : s∈G.faceSourcePorts F)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (hneF : G.sourceFace e≠F) :
    edgeComponent e≠edgeComponent s := by
  intro hc
  have he : SpineSource e := G.spineSource_of_sourceFace_mem_defects ht e heF
  have hne : e≠s := by
    intro h
    exact hneF (h ▸ (Finset.mem_filter.mp hs).2.2)
  exact G.boundary_face_other_source_end_unbounded ht hY F hFY hports hs he hc.symm hne
    (G.defectPlaneFace_isBounded ht heF)

structure PentagonSpokeLoops {n : ℕ} (G : PennyGraph n) (F : PlaneFace G)
    (P : PentagonFaceBoundary G F) where
  outer : PlaneFace G
  outer_unbounded : ¬Bornology.IsBounded outer.val
  loop : (i : Fin 5) → PlaneChain (edgeCenter (P.dart i)) (edgeCenter (P.dart i))
  finish : Fin 5→OrientedEdge G
  spine : (i : Fin 5) → PositiveSpineChain G (P.dart i) (finish i)
  sink : ∀ i,¬∃g,PositiveCellStep (finish i) g
  contains_first : ∀ i,trackSpineTrace (edgeComponent (P.dart i))⊆(loop i).trace
  contains_second : ∀ i,trackSpineTrace (edgeComponent (P.dart (i+1)))⊆(loop i).trace
  support : ∀ i,G.SpokePairSupport (edgeComponent (P.dart i))
    (edgeComponent (P.dart (i+1))) F outer (loop i)
  bank_disjoint : ∀ i sign,sign=1 ∨ sign= -1 → Disjoint ((spine i).bankRegion sign) (loop i).trace
  bank_difference : ∀ i,
    (spine i).bankLabel (loop i) (-1)=(spine i).bankLabel (loop i) 1+1

theorem PentagonFaceBoundary.exists_spoke_loops {n : ℕ} {G : PennyGraph n} {F : PlaneFace G}
    (P : PentagonFaceBoundary G F) (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y) :
    Nonempty (PentagonSpokeLoops G F P) := by
  obtain ⟨outer,houter,_⟩ := G.exists_unique_outer_face
  have hport (i : Fin 5) : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hne (i : Fin 5) : edgeComponent (P.dart i)≠edgeComponent (P.dart (i+1)) := by
    intro hc
    have heq := G.boundary_face_port_component_injective ht hY F hFY hports (hport i) (hport (i+1)) hc
    have hidx := P.vertex_injective (congrArg (fun e : OrientedEdge G => e.val.1) heq)
    have hbad : i≠i+1 := by fin_cases i <;> decide
    exact hbad hidx
  have hmiss (i : Fin 5) := P.source_tracks_noncrossing ht (hY.subset_defects hFY)
    (P.dart i) (P.dart (i+1)) (hport i) (hport (i+1))
  have hex (i : Fin 5) := G.boundary_spoke_pair_banks_full ht hY F hFY hports outer houter
    (P.dart i) (P.dart (i+1)) (hport i) (hport (i+1)) (hne i) (hmiss i)
  choose finish spine sink loop hsupport hfirst hsecond hdis hdiff using hex
  exact ⟨{
    outer := outer
    outer_unbounded := houter
    loop := loop
    finish := finish
    spine := spine
    sink := sink
    contains_first := hfirst
    contains_second := hsecond
    support := hsupport
    bank_disjoint := hdis
    bank_difference := hdiff
  }⟩

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

def code (H : PlaneFace G) : Fin 5→ℤ := fun i => G.faceWindingLabel (K.loop i) H

theorem bank_difference_of_step (i : Fin 5) (_hstep : ∃d,PositiveCellStep (P.dart i) d) :
    (K.spine i).bankLabel (K.loop i) (-1)=(K.spine i).bankLabel (K.loop i) 1+1 :=
  K.bank_difference i

theorem bank_labels_distinct (i : Fin 5) :
    (K.spine i).bankLabel (K.loop i) 1≠(K.spine i).bankLabel (K.loop i) (-1) := by
  have h := K.bank_difference i
  omega

theorem bank_labels_distinct_of_step (i : Fin 5) (hstep : ∃d,PositiveCellStep (P.dart i) d) :
    (K.spine i).bankLabel (K.loop i) 1≠(K.spine i).bankLabel (K.loop i) (-1) := by
  have h := K.bank_difference_of_step i hstep
  omega

theorem bank_labels_distinct_of_crossing (ht : G.TriangleFree) (i : Fin 5) (v : TrackComponent G)
    (hcross : ComponentCrosses (edgeComponent (P.dart i)) v) :
    (K.spine i).bankLabel (K.loop i) 1≠(K.spine i).bankLabel (K.loop i) (-1) := by
  have hport : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  obtain ⟨q,_,hprefix,_⟩ := crossing_cut_transition_before_source ht v (P.dart i)
    (Finset.mem_filter.mp hport).2.1 ((componentGraph G ht).ne_of_adj hcross) hcross
  obtain ⟨d,hsd,_⟩ := Relation.TransGen.head'_iff.mp (Relation.TransGen.tail' hprefix q.property)
  exact K.bank_labels_distinct_of_step i ⟨d,hsd⟩

theorem code_at_point (ht : G.TriangleFree) (H : PlaneFace G) (hH : H∈G.defectPlaneFaces ht)
    (hHF : H≠F) (z : Plane) (hz : z∈H.val) :
    (fun i => (K.loop i).windingIndex z)=K.code H := by
  funext i
  exact (K.support i).defect_winding_constant ht K.outer_unbounded H hH hHF z hz

theorem zero_crossing_join_code_eq (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (e f : OrientedEdge G) (heF : G.sourceFace e∈G.defectPlaneFaces ht)
    (hfF : G.sourceFace f∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F) (hfRoot : G.sourceFace f≠F)
    (hcomp : edgeComponent f=edgeComponent e)
    (hmiss : ∀ i : Fin 5,¬ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i))) :
    K.code (G.sourceFace e)=K.code (G.sourceFace f) := by
  have hport (i : Fin 5) : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hne (i : Fin 5) := G.boundary_face_other_defect_component_ne ht hY F hFY hports
    (P.dart i) e (hport i) heF heRoot
  funext i
  exact (K.support i).noncrossing_source_face_labels_eq ht (hY.subset_defects hFY) K.outer_unbounded
    e f heF hfF heRoot hfRoot hcomp (hne i) (hne (i+1)) (hmiss i) (hmiss (i+1))

end PentagonSpokeLoops
end Swanepoel
