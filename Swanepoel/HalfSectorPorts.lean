module
public import Swanepoel.HalfAnchorCounting
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure HalfSectorPorts {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (cut nonAnchor : TrackComponent G) (Y : Finset (PlaneFace G)) (Label : Type*) where
  subset_defects : Y⊆G.defectPlaneFaces ht
  code : PlaneFace G → Label
  direction : Label → Plane
  direction_ne_zero : ∀ s, direction s≠0
  missing : ∀ F∈Y, ∀ e∈G.faceSourcePorts F,
    0 < inner ℝ (direction (code F)) (sourceNormal e) →
      ¬ComponentCrosses cut (edgeComponent e) ∧ ¬ComponentCrosses nonAnchor (edgeComponent e)
  same_code : ∀ e f : OrientedEdge G, SpineSource e → G.sourceFace e∈Y →
    SpineSource f → G.sourceFace f∈Y → edgeComponent e=edgeComponent f →
    ¬ComponentCrosses cut (edgeComponent e) → ¬ComponentCrosses nonAnchor (edgeComponent e) →
      code (G.sourceFace e)=code (G.sourceFace f)

namespace HalfSectorPorts
variable {n : ℕ} {G : PennyGraph n} {ht : G.TriangleFree}
    {cut v : TrackComponent G} {Y : Finset (PlaneFace G)} {Label : Type*}
    (D : HalfSectorPorts G ht cut v Y Label)

def selected : Finset (OrientedEdge G) := (G.familySourcePorts Y).filter
  (fun e => 0 < inner ℝ (D.direction (D.code (G.sourceFace e))) (sourceNormal e))

theorem selected_source {e : OrientedEdge G} (he : e∈D.selected) : SpineSource e :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.1

theorem selected_face {e : OrientedEdge G} (he : e∈D.selected) : G.sourceFace e∈Y :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2

theorem selected_missing {e : OrientedEdge G} (he : e∈D.selected) :
    ¬ComponentCrosses cut (edgeComponent e) ∧ ¬ComponentCrosses v (edgeComponent e) := by
  apply D.missing (G.sourceFace e) (D.selected_face he) e
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,D.selected_source he,rfl⟩
  · exact (Finset.mem_filter.mp he).2

theorem selected_component_injective : Set.InjOn edgeComponent (D.selected : Set (OrientedEdge G)) := by
  intro e he f hf hc
  have hcode := D.same_code e f (D.selected_source he) (D.selected_face he)
    (D.selected_source hf) (D.selected_face hf) hc (D.selected_missing he).1 (D.selected_missing he).2
  have hp := (Finset.mem_filter.mp he).2
  have hq := (Finset.mem_filter.mp hf).2
  rw [← hcode] at hq
  exact source_component_injective_in_open_semicircle ht _ (D.selected_source he)
    (D.selected_source hf) hp hq hc

theorem selected_fiber (F : PlaneFace G) (hF : F∈Y) :
    D.selected.filter (fun e => G.sourceFace e=F)=
      (G.faceSourcePorts F).filter (fun e => 0 < inner ℝ (D.direction (D.code F)) (sourceNormal e)) := by
  ext e
  simp only [selected,PennyGraph.familySourcePorts,PennyGraph.faceSourcePorts,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨⟨hs,_⟩,hp⟩,heq⟩
    exact ⟨⟨hs,heq⟩,by simpa only [heq] using hp⟩
  · rintro ⟨⟨hs,heq⟩,hp⟩
    exact ⟨⟨⟨hs,heq ▸ hF⟩,by simpa only [heq] using hp⟩,heq⟩

theorem selected_card_lower
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b) :
    2*Y.card≤D.selected.card := by
  have hcard := Finset.card_eq_sum_card_fiberwise (f := G.sourceFace)
    (s := D.selected) (t := Y) (fun e he => D.selected_face he)
  calc
    _ = ∑ _∈Y, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ F∈Y, (D.selected.filter (fun e => G.sourceFace e=F)).card := by
      apply Finset.sum_le_sum
      intro F hF
      rw [D.selected_fiber F hF]
      exact G.defect_two_semicircle_ports ht F (D.subset_defects hF) hdegree _ (D.direction_ne_zero _)
    _ = _ := hcard.symm

include D

theorem anchor_count
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (hcross : ComponentCrosses cut v) :
    (((G.familyTrackComponents Y).filter (ComponentCrosses v)).card : ℤ)≤
      (G.familyTrackComponents Y).card-
      ((G.familyTrackComponents Y).filter (ComponentCrosses cut)).card-2*Y.card := by
  let A := G.familyTrackComponents Y
  let U := A.filter (ComponentCrosses cut)
  let V := A.filter (ComponentCrosses v)
  let P := D.selected.image edgeComponent
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro c hcU hcV
    exact componentGraph_noTriple G ht cut v c hcross (Finset.mem_filter.mp hcV).2
      ((componentGraph G ht).adj_symm (Finset.mem_filter.mp hcU).2)
  have hUP : Disjoint U P := by
    apply Finset.disjoint_left.mpr
    intro c hcU hcP
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hcP
    exact (D.selected_missing he).1 (Finset.mem_filter.mp hcU).2
  have hVP : Disjoint V P := by
    apply Finset.disjoint_left.mpr
    intro c hcV hcP
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hcP
    exact (D.selected_missing he).2 (Finset.mem_filter.mp hcV).2
  have hPsub : P⊆A := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨e,(Finset.mem_filter.mp he).1,rfl⟩
  have hPcard : P.card=D.selected.card := Finset.card_image_of_injOn D.selected_component_injective
  have hsub : (U∪V)∪P⊆A := Finset.union_subset
    (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) hPsub
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hUP,hVP⟩),
    Finset.card_union_of_disjoint hUV,hPcard] at hcount
  have hlo := D.selected_card_lower hdegree
  change (V.card:ℤ)≤A.card-U.card-2*Y.card
  omega

end HalfSectorPorts
end Swanepoel
