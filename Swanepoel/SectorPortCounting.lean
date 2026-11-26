module
public import Swanepoel.DefectSemicircleTracks
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

structure SectorPortData {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (u v : TrackComponent G) (Label : Type*) where
  code : PlaneFace G → Label
  direction : Label → Plane
  direction_ne_zero : ∀ s, direction s≠0
  missing : ∀ F∈G.defectPlaneFaces ht, ∀ e∈G.faceSourcePorts F,
    0 < inner ℝ (direction (code F)) (sourceNormal e) →
      ¬ComponentCrosses u (edgeComponent e) ∧ ¬ComponentCrosses v (edgeComponent e)
  same_code : ∀ e f : OrientedEdge G,
    SpineSource e → G.sourceFace e∈G.defectPlaneFaces ht →
    SpineSource f → G.sourceFace f∈G.defectPlaneFaces ht →
    edgeComponent e=edgeComponent f →
    ¬ComponentCrosses u (edgeComponent e) → ¬ComponentCrosses v (edgeComponent e) →
      code (G.sourceFace e)=code (G.sourceFace f)

namespace SectorPortData
variable {n : ℕ} {G : PennyGraph n} {ht : G.TriangleFree}
    {u v : TrackComponent G} {Label : Type*} (D : SectorPortData G ht u v Label)

def selected : Finset (OrientedEdge G) :=
  Finset.univ.filter (fun e => SpineSource e ∧ G.sourceFace e∈G.defectPlaneFaces ht ∧
    0 < inner ℝ (D.direction (D.code (G.sourceFace e))) (sourceNormal e))

theorem selected_source {e : OrientedEdge G} (he : e∈D.selected) : SpineSource e :=
  (Finset.mem_filter.mp he).2.1

theorem selected_face {e : OrientedEdge G} (he : e∈D.selected) :
    G.sourceFace e∈G.defectPlaneFaces ht := (Finset.mem_filter.mp he).2.2.1

theorem selected_positive {e : OrientedEdge G} (he : e∈D.selected) :
    0 < inner ℝ (D.direction (D.code (G.sourceFace e))) (sourceNormal e) :=
  (Finset.mem_filter.mp he).2.2.2

theorem selected_missing {e : OrientedEdge G} (he : e∈D.selected) :
    ¬ComponentCrosses u (edgeComponent e) ∧ ¬ComponentCrosses v (edgeComponent e) :=
  D.missing (G.sourceFace e) (D.selected_face he) e
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,D.selected_source he,rfl⟩) (D.selected_positive he)

theorem selected_terminal {e : OrientedEdge G} (he : e∈D.selected) :
    edgeComponent e∈G.terminalTrackComponents :=
  (G.terminal_iff_defect_source ht (edgeComponent e)).mpr
    ⟨e,D.selected_source he,rfl,D.selected_face he⟩

theorem selected_component_injective : Set.InjOn edgeComponent (D.selected : Set (OrientedEdge G)) := by
  intro e he f hf hcomp
  have hmiss := D.selected_missing he
  have hcode := D.same_code e f (D.selected_source he) (D.selected_face he)
    (D.selected_source hf) (D.selected_face hf) hcomp hmiss.1 hmiss.2
  have hfpos := D.selected_positive hf
  rw [← hcode] at hfpos
  exact source_component_injective_in_open_semicircle ht _ (D.selected_source he)
    (D.selected_source hf) (D.selected_positive he) hfpos hcomp

theorem selected_component_card : (D.selected.image edgeComponent).card=D.selected.card :=
  Finset.card_image_of_injOn D.selected_component_injective

theorem selected_face_fiber (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) :
    D.selected.filter (fun e => G.sourceFace e=F) =
      (G.faceSourcePorts F).filter (fun e => 0 < inner ℝ (D.direction (D.code F)) (sourceNormal e)) := by
  ext e
  constructor
  · intro he
    have he' := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,D.selected_source he'.1,he'.2⟩,?_⟩
    simpa only [he'.2] using D.selected_positive he'.1
  · intro he
    have he' := Finset.mem_filter.mp he
    have hport := (Finset.mem_filter.mp he'.1).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hport.1,?_,?_⟩,hport.2⟩
    · rw [hport.2]
      exact hF
    · simpa only [hport.2] using he'.2

theorem selected_card_lower
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b) :
    2*G.faceDefectCount ht≤D.selected.card := by
  have hcard := Finset.card_eq_sum_card_fiberwise (f := G.sourceFace)
    (s := D.selected) (t := G.defectPlaneFaces ht) (fun e he => D.selected_face he)
  have hlo : 2*(G.defectPlaneFaces ht).card≤
      ∑ F∈G.defectPlaneFaces ht, (D.selected.filter (fun e => G.sourceFace e=F)).card := by
    calc
      _ = ∑ _∈G.defectPlaneFaces ht, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun F hF => by
        rw [D.selected_face_fiber F hF]
        exact G.defect_two_semicircle_ports ht F hF hdegree _ (D.direction_ne_zero _))
  rw [G.defectPlaneFaces_card ht,← hcard] at hlo
  exact hlo

include D

theorem terminal_crossing_count
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (huv : ComponentCrosses u v) :
    (G.terminalTrackComponents.filter (ComponentCrosses u)).card +
      (G.terminalTrackComponents.filter (ComponentCrosses v)).card +
      2*G.faceDefectCount ht ≤ G.terminalTrackComponents.card := by
  let A := G.terminalTrackComponents
  let U := A.filter (ComponentCrosses u)
  let V := A.filter (ComponentCrosses v)
  let P := D.selected.image edgeComponent
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro c hcU hcV
    exact componentGraph_noTriple G ht u v c huv (Finset.mem_filter.mp hcV).2
      (((componentGraph G ht).adj_comm _ _).mp (Finset.mem_filter.mp hcU).2)
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
  have hsub : (U∪V)∪P⊆A := by
    apply Finset.union_subset
    · exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · intro c hc
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
      exact D.selected_terminal he
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hUP,hVP⟩),
    Finset.card_union_of_disjoint hUV,D.selected_component_card] at hcount
  have hlower := D.selected_card_lower hdegree
  change U.card+V.card+2*G.faceDefectCount ht≤A.card
  omega

end SectorPortData

theorem PennyGraph.componentSystem_s_eq_terminal_neighbors {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (f : ℕ) (u : Fin (Fintype.card (TrackComponent G))) :
    (componentSystem G ht G.ordinaryTrackComponents f).s u =
      (G.terminalTrackComponents.filter
        (ComponentCrosses ((Fintype.equivFin (TrackComponent G)).symm u))).card := by
  let E := Fintype.equivFin (TrackComponent G)
  have hterminal (i : Fin (Fintype.card (TrackComponent G))) :
      i∈(Finset.univ \ G.ordinaryTrackComponents.map E.toEmbedding) ↔
        E.symm i∈G.terminalTrackComponents := by
    rw [Finset.mem_sdiff,G.mem_terminalTrackComponents]
    simp only [Finset.mem_univ,true_and,Finset.mem_map_equiv]
  change ((Finset.univ \ G.ordinaryTrackComponents.map E.toEmbedding).filter
    (fun i : Fin (Fintype.card (TrackComponent G)) => ComponentCrosses (E.symm u) (E.symm i))).card =
    (G.terminalTrackComponents.filter (ComponentCrosses (E.symm u))).card
  refine Finset.card_bij (fun i _ => E.symm i) ?_ ?_ ?_
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(hterminal i).mp hi'.1,hi'.2⟩
  · intro i _ j _ h
    exact E.symm.injective h
  · intro c hc
    have hc' := Finset.mem_filter.mp hc
    refine ⟨E c,Finset.mem_filter.mpr ⟨?_,?_⟩,E.symm_apply_apply c⟩
    · apply (hterminal (E c)).mpr
      simpa only [Equiv.symm_apply_apply] using hc'.1
    · rw [E.symm_apply_apply]
      exact hc'.2

theorem PennyGraph.crossing_pair_bound_of_sector_data {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Label : Type*)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (hsector : ∀ u∈G.ordinaryTrackComponents, ∀ v∈G.ordinaryTrackComponents,
      ComponentCrosses u v → Nonempty (SectorPortData G ht u v Label)) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).CrossingPairBound := by
  let E := Fintype.equivFin (TrackComponent G)
  let T := componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)
  intro u hu v hv huv
  have hu' : E.symm u∈G.ordinaryTrackComponents := Finset.mem_map_equiv.mp hu
  have hv' : E.symm v∈G.ordinaryTrackComponents := Finset.mem_map_equiv.mp hv
  have huv' : ComponentCrosses (E.symm u) (E.symm v) := huv
  obtain ⟨D⟩ := hsector _ hu' _ hv' huv'
  have hnat := D.terminal_crossing_count hdegree huv'
  have hint : ((G.terminalTrackComponents.filter (ComponentCrosses (E.symm u))).card : ℤ) +
      (G.terminalTrackComponents.filter (ComponentCrosses (E.symm v))).card +
      2*G.faceDefectCount ht ≤ G.terminalTrackComponents.card := by exact_mod_cast hnat
  rw [G.componentSystem_s_eq_terminal_neighbors ht _ u,G.componentSystem_s_eq_terminal_neighbors ht _ v,
    G.componentSystem_K_eq]
  exact sub_nonneg.mp (by omega : 0≤(G.terminalTrackComponents.card : ℤ)-2*G.faceDefectCount ht-
    (((G.terminalTrackComponents.filter (ComponentCrosses (E.symm u))).card : ℤ)+
      (G.terminalTrackComponents.filter (ComponentCrosses (E.symm v))).card))

end Swanepoel
