module
public import Swanepoel.JoinClosedCrossings
public import Swanepoel.BoundaryPortPairing
public import Swanepoel.QuadraticBoundaryCase
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.large_boundary_exists_five_port_boundary_face {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (hlarge : 8*G.familyK Y < 5*(G.familyBoundaryEndCount Y : ℤ)) :
    ∃ F ∈ Y, (G.faceSourcePorts F).card = 5 ∧
      ∀ e ∈ G.faceSourcePorts F, edgeComponent e ∈ G.familyBoundaryTrackComponents Y := by
  have hB : (G.familyBoundaryEndCount Y : ℤ) =
      ∑ F ∈ Y, (G.familyBoundaryPortCount Y F : ℤ) := by
    exact_mod_cast (G.sum_familyBoundaryPortCount ht hY).symm
  have hK : 2*G.familyK Y = (G.familyBoundaryEndCount Y : ℤ)+
      ∑ F ∈ Y, (((G.faceSourcePorts F).card : ℤ)-4) := by
    exact G.family_K_port_conservation ht hY
  obtain ⟨F,hFY,hfive,hbfive⟩ := large_boundary_exists_full_pentagon Y
    (fun F => (G.faceSourcePorts F).card) (G.familyBoundaryPortCount Y)
    (G.familyK Y) (G.familyBoundaryEndCount Y)
    (fun F hF => G.defect_source_ports_five_le ht F (hY.subset_defects hF))
    (fun F _ => G.familyBoundaryPortCount_le Y F) hB hK hlarge
  refine ⟨F,hFY,hfive,?_⟩
  have heq : (G.faceSourcePorts F).filter
      (fun e => edgeComponent e ∈ G.familyBoundaryTrackComponents Y) = G.faceSourcePorts F := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    change (G.faceSourcePorts F).card ≤ G.familyBoundaryPortCount Y F
    rw [hfive,hbfive]
  intro e he
  have hem : e ∈ (G.faceSourcePorts F).filter
      (fun e => edgeComponent e ∈ G.familyBoundaryTrackComponents Y) := by rwa [heq]
  exact (Finset.mem_filter.mp hem).2

theorem PennyGraph.familySourcePorts_singleton {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    G.familySourcePorts {F} = G.faceSourcePorts F := by
  ext e
  simp only [PennyGraph.familySourcePorts, PennyGraph.faceSourcePorts, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]

theorem PennyGraph.boundary_face_other_source_end_unbounded {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F ∈ Y)
    (hports : ∀ e ∈ G.faceSourcePorts F, edgeComponent e ∈ G.familyBoundaryTrackComponents Y)
    {e f : OrientedEdge G} (he : e ∈ G.faceSourcePorts F) (hf : SpineSource f)
    (hc : edgeComponent e = edgeComponent f) (hne : f ≠ e) :
    ¬ Bornology.IsBounded (G.sourceFace f).val := by
  intro hb
  have hep := (Finset.mem_filter.mp he).2
  have heY : G.sourceFace e ∈ Y := by rwa [hep.2]
  have heport : e ∈ G.familySourcePorts Y :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,heY⟩
  have hfdef := (G.sourceFace_defect_or_unbounded ht f hf).resolve_right (fun hn => hn hb)
  have hfY := hY.other_bounded_end e f hep.1 hf hc heY hfdef
  have hfport : f ∈ G.familySourcePorts Y := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf,hfY⟩
  exact hne (G.bounded_sources_eq_on_boundary_track ht hY heport hfport hc (hports e he)).symm

theorem PennyGraph.boundary_face_singleton_joinClosed {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F ∈ Y)
    (hports : ∀ e ∈ G.faceSourcePorts F, edgeComponent e ∈ G.familyBoundaryTrackComponents Y) :
    G.IsJoinClosed ht {F} := by
  refine ⟨Finset.singleton_subset_iff.mpr (hY.subset_defects hFY),?_⟩
  intro e f he hf hc heF hfdef
  have heface : G.sourceFace e = F := Finset.mem_singleton.mp heF
  have heport : e ∈ G.faceSourcePorts F :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heface⟩
  by_cases hfe : f = e
  · simpa only [hfe] using heF
  · exact False.elim (G.boundary_face_other_source_end_unbounded ht hY F hFY hports
      heport hf hc hfe (G.defectPlaneFace_isBounded ht hfdef))

theorem PennyGraph.boundary_face_singleton_track_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F ∈ Y)
    (hports : ∀ e ∈ G.faceSourcePorts F, edgeComponent e ∈ G.familyBoundaryTrackComponents Y) :
    (G.familyTrackComponents {F}).card = (G.faceSourcePorts F).card := by
  have hinj : Set.InjOn edgeComponent (G.faceSourcePorts F : Set (OrientedEdge G)) := by
    intro e he f hf hc
    have heY : e ∈ G.familySourcePorts Y := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2.1,
        (Finset.mem_filter.mp he).2.2 ▸ hFY⟩
    have hfY : f ∈ G.familySourcePorts Y := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp hf).2.1,
        (Finset.mem_filter.mp hf).2.2 ▸ hFY⟩
    exact G.bounded_sources_eq_on_boundary_track ht hY heY hfY hc (hports e he)
  rw [PennyGraph.familyTrackComponents, G.familySourcePorts_singleton]
  exact Finset.card_image_of_injOn hinj

theorem PennyGraph.boundary_five_port_singleton_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F ∈ Y) (hfive : (G.faceSourcePorts F).card = 5)
    (hports : ∀ e ∈ G.faceSourcePorts F, edgeComponent e ∈ G.familyBoundaryTrackComponents Y) :
    G.familyK {F} = 3 := by
  rw [PennyGraph.familyK, G.boundary_face_singleton_track_count ht hY F hFY hports,
    hfive, Finset.card_singleton]
  norm_num

theorem PennyGraph.large_boundary_exists_five_port_removal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (hlarge : 8*G.familyK Y < 5*(G.familyBoundaryEndCount Y : ℤ)) :
    ∃ F ∈ Y, (G.faceSourcePorts F).card = 5 ∧ G.IsJoinClosed ht {F} ∧
      (G.familyTrackComponents {F}).card = 5 ∧ G.familyK {F} = 3 ∧
      G.IsJoinClosed ht (Y \ {F}) ∧ G.familyK Y = 3+G.familyK (Y \ {F}) ∧
      (Y \ {F}).card+1 = Y.card := by
  obtain ⟨F,hFY,hfive,hports⟩ := G.large_boundary_exists_five_port_boundary_face ht hY hlarge
  have hFclosed := G.boundary_face_singleton_joinClosed ht hY F hFY hports
  have htracks : (G.familyTrackComponents {F}).card = 5 := by
    rw [G.boundary_face_singleton_track_count ht hY F hFY hports,hfive]
  have hK := G.boundary_five_port_singleton_K ht hY F hFY hfive hports
  have hrest := hY.sdiff hFclosed
  have hsub : ({F} : Finset (PlaneFace G)) ⊆ Y := Finset.singleton_subset_iff.mpr hFY
  have hunion : ({F} : Finset (PlaneFace G)) ∪ (Y \ {F}) = Y :=
    Finset.union_sdiff_of_subset hsub
  have hdis : Disjoint ({F} : Finset (PlaneFace G)) (Y \ {F}) := Finset.disjoint_left.mpr (by
    intro H hHF hHrest
    exact (Finset.mem_sdiff.mp hHrest).2 hHF)
  have hKsplit : G.familyK Y = 3+G.familyK (Y \ {F}) := by
    calc
      _ = G.familyK ({F} ∪ (Y \ {F})) := congrArg (G.familyK) hunion.symm
      _ = G.familyK {F}+G.familyK (Y \ {F}) := G.familyK_union ht hFclosed hrest hdis
      _ = _ := by rw [hK]
  have hcard : (Y \ {F}).card+1 = Y.card := by
    simpa only [Finset.card_singleton] using Finset.card_sdiff_add_card_eq_card hsub
  exact ⟨F,hFY,hfive,hFclosed,htracks,hK,hrest,hKsplit,hcard⟩

end Swanepoel
