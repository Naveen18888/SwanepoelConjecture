module
public import Swanepoel.TrackCutSources
public import Mathlib.Data.List.Chain
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def planeSegmentStep (F : Set Plane) (x y : Plane) : Prop := segment ℝ x y⊆F

theorem open_preconnected_plane_segment_reachable {F : Set Plane}
    (hF : IsOpen F) (hconn : IsPreconnected F) {a b : Plane} (ha : a∈F) (hb : b∈F) :
    Relation.ReflTransGen (planeSegmentStep F) a b := by
  let R : Set Plane := {x | x∈F ∧ Relation.ReflTransGen (planeSegmentStep F) a x}
  have hR : IsOpen R := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hF x hx.1
    refine ⟨r,hr,?_⟩
    intro y hy
    exact ⟨hball hy,hx.2.tail (((convex_ball x r).segment_subset (Metric.mem_ball_self hr) hy).trans hball)⟩
  have hD : IsOpen (F\R) := by
    apply Metric.isOpen_iff.mpr
    rintro x ⟨hxF,hxR⟩
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hF x hxF
    refine ⟨r,hr,?_⟩
    intro y hy
    refine ⟨hball hy,?_⟩
    intro hyR
    apply hxR
    exact ⟨hxF,hyR.2.tail (((convex_ball x r).segment_subset hy (Metric.mem_ball_self hr)).trans hball)⟩
  have hdis : Disjoint R (F\R) := Set.disjoint_sdiff_right
  have hcover : F⊆R∪(F\R) := by
    intro x hx
    by_cases h : x∈R
    · exact Or.inl h
    · exact Or.inr ⟨hx,h⟩
  have hstart : (F∩R).Nonempty := ⟨a,ha,ha,Relation.ReflTransGen.refl⟩
  exact (hconn.subset_left_of_subset_union hR hD hdis hcover hstart hb).2

theorem plane_segment_reachable_list {F : Set Plane} {a b : Plane} (ha : a∈F)
    (hab : Relation.ReflTransGen (planeSegmentStep F) a b) :
    ∃ vertices : List Plane,
      vertices.head?=some a ∧ vertices.getLast?=some b ∧
      vertices.IsChain (planeSegmentStep F) ∧ ∀ x∈vertices, x∈F := by
  induction hab with
  | refl => exact ⟨[a],by simp,by simp,by simp,by simp [ha]⟩
  | @tail b c hab hbc ih =>
    obtain ⟨vertices,hhead,hlast,hchain,hinside⟩ := ih
    have hne : vertices≠[] := by intro he; simp only [he,List.head?_nil] at hhead; contradiction
    refine ⟨vertices++[c],?_,?_,?_,?_⟩
    · rwa [List.head?_append_of_ne_nil vertices hne]
    · simp
    · apply hchain.append (by simp)
      intro x hx y hy
      have hxb : b=x := by simpa only [hlast,Option.mem_some_iff] using hx
      have hyc : c=y := by simpa using hy
      simpa only [hxb,hyc] using hbc
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hinside x hx
      · have hxc : x=c := by simpa using hx
        subst x
        exact hbc (right_mem_segment ℝ b c)

theorem PennyGraph.face_segment_reachable {n : ℕ} (G : PennyGraph n) (F : PlaneFace G)
    {a b : Plane} (ha : a∈F.val) (hb : b∈F.val) :
    Relation.ReflTransGen (planeSegmentStep F.val) a b := by
  have hpre : IsPreconnected F.val := by
    obtain ⟨x,hx,hF⟩ := F.property
    rw [hF]
    exact isPreconnected_connectedComponentIn
  exact open_preconnected_plane_segment_reachable F.property.isOpen hpre ha hb

theorem PennyGraph.ordinary_track_outer_segment_chain {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) (hc : c∈G.ordinaryTrackComponents) :
    ∃ s t : OrientedEdge G, s≠t ∧ SpineSource s ∧ SpineSource t ∧
      edgeComponent s=c ∧ edgeComponent t=c ∧
      ∃ outer : PlaneFace G, ¬Bornology.IsBounded outer.val ∧
        G.sourceFace s=outer ∧ G.sourceFace t=outer ∧
        ∃ vertices : List Plane,
          vertices.head?=some (G.sourceProbe s) ∧ vertices.getLast?=some (G.sourceProbe t) ∧
          vertices.IsChain (planeSegmentStep outer.val) ∧
          vertices.IsChain (planeSegmentStep G.drawingᶜ) ∧ ∀ x∈vertices, x∈outer.val := by
  obtain ⟨s,t,hne,hall⟩ := component_sources ht c
  have hs := (hall s).mpr (Or.inl rfl)
  have hts := (hall t).mpr (Or.inr rfl)
  obtain ⟨outer,houter,_⟩ := G.exists_unique_outer_face
  have hfaces := (G.ordinary_iff_sourceFace_eq_outer c outer houter).mp hc
  have hsF := hfaces s hs.1 hs.2
  have htF := hfaces t hts.1 hts.2
  have hsp : G.sourceProbe s∈outer.val := by rw [← hsF]; exact G.sourceProbe_mem_sourceFace s
  have htp : G.sourceProbe t∈outer.val := by rw [← htF]; exact G.sourceProbe_mem_sourceFace t
  have hreach := G.face_segment_reachable outer hsp htp
  obtain ⟨vertices,hhead,hlast,hchain,hinside⟩ := plane_segment_reachable_list hsp hreach
  have hsub : outer.val⊆G.drawingᶜ := by
    obtain ⟨x,hx,hF⟩ := outer.property
    rw [hF]
    exact connectedComponentIn_subset _ _
  refine ⟨s,t,hne,hs.1,hts.1,hs.2,hts.2,outer,houter,hsF,htF,
    vertices,hhead,hlast,hchain,?_,hinside⟩
  exact hchain.imp (fun _ _ h => h.trans hsub)

end Swanepoel
