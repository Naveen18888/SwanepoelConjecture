module
public import Swanepoel.HalfPieceBanks
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.familyPortFiber {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) (c : TrackComponent G) : Finset (OrientedEdge G) :=
  (G.familySourcePorts Y).filter (fun e => edgeComponent e=c)

def PennyGraph.familyUnpairedTracks {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) : Finset (TrackComponent G) :=
  (G.familyTrackComponents Y).filter (fun c => (G.familyPortFiber Y c).card=1)

def PennyGraph.familyUnpairedPorts {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) : Finset (OrientedEdge G) :=
  (G.familySourcePorts Y).filter (fun e => edgeComponent e∈G.familyUnpairedTracks Y)

theorem PennyGraph.familyPortFiber_card_le_two {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (c : TrackComponent G) :
    (G.familyPortFiber Y c).card≤2 := by
  rw [← component_source_count ht c]
  apply Finset.card_le_card
  intro e he
  have hep := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hep.1).2.1,hep.2⟩

theorem PennyGraph.familyPortFiber_nonempty_iff {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) (c : TrackComponent G) :
    (G.familyPortFiber Y c).Nonempty ↔ c∈G.familyTrackComponents Y := by
  constructor
  · rintro ⟨e,he⟩
    exact Finset.mem_image.mpr ⟨e,(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
  · intro hc
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hc
    exact ⟨e,Finset.mem_filter.mpr ⟨he,hec⟩⟩

theorem PennyGraph.familyPortFiber_card_one_or_two {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) {c : TrackComponent G}
    (hc : c∈G.familyTrackComponents Y) :
    (G.familyPortFiber Y c).card=1 ∨ (G.familyPortFiber Y c).card=2 := by
  have hp := ((G.familyPortFiber_nonempty_iff Y c).mpr hc).card_pos
  have hb := G.familyPortFiber_card_le_two ht Y c
  omega

theorem PennyGraph.familyUnpairedPorts_component_injOn {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) :
    Set.InjOn edgeComponent (G.familyUnpairedPorts Y : Set (OrientedEdge G)) := by
  intro e he f hf hc
  have he' := Finset.mem_filter.mp he
  have hf' := Finset.mem_filter.mp hf
  have hone := (Finset.mem_filter.mp he'.2).2
  apply Finset.card_le_one.mp hone.le
  · exact Finset.mem_filter.mpr ⟨he'.1,rfl⟩
  · exact Finset.mem_filter.mpr ⟨hf'.1,hc.symm⟩

theorem PennyGraph.familyUnpairedPorts_image {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) :
    (G.familyUnpairedPorts Y).image edgeComponent=G.familyUnpairedTracks Y := by
  ext c
  constructor
  · rintro hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp he).2
  · intro hc
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hec ▸ hc⟩,hec⟩

theorem PennyGraph.familyUnpairedPorts_card {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) :
    (G.familyUnpairedPorts Y).card=(G.familyUnpairedTracks Y).card := by
  rw [← G.familyUnpairedPorts_image Y,Finset.card_image_of_injOn (G.familyUnpairedPorts_component_injOn Y)]

theorem PennyGraph.partial_family_endpoint_conservation {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) :
    2*(G.familyTrackComponents Y).card=
      (G.familySourcePorts Y).card+(G.familyUnpairedPorts Y).card := by
  have hports := Finset.card_eq_sum_card_fiberwise (f := edgeComponent)
    (s := G.familySourcePorts Y) (t := G.familyTrackComponents Y)
    (fun e he => Finset.mem_image.mpr ⟨e,he,rfl⟩)
  have hBsum : (G.familyUnpairedTracks Y).card=∑ c∈G.familyTrackComponents Y,
      (if (G.familyPortFiber Y c).card=1 then 1 else 0) := by
    rw [familyUnpairedTracks,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [G.familyUnpairedPorts_card Y,hports,hBsum]
  change 2*(G.familyTrackComponents Y).card=
    (∑ c∈G.familyTrackComponents Y,(G.familyPortFiber Y c).card)+
      ∑ c∈G.familyTrackComponents Y,(if (G.familyPortFiber Y c).card=1 then 1 else 0)
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _∈G.familyTrackComponents Y, 2 := by simp [Nat.mul_comm]
    _ = _ := Finset.sum_congr rfl (by
      intro c hc
      rcases G.familyPortFiber_card_one_or_two ht Y hc with h | h <;> simp [h])

theorem PennyGraph.partial_family_K_port_conservation {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) :
    2*G.familyK Y=(G.familyUnpairedPorts Y).card+G.familyPortExcess Y := by
  have hc := G.partial_family_endpoint_conservation ht Y
  have hp : ((G.familySourcePorts Y).card : ℤ)=∑ F∈Y,((G.faceSourcePorts F).card : ℤ) := by
    exact_mod_cast G.familySourcePorts_card Y
  rw [PennyGraph.familyK,G.familyPortExcess_eq]
  omega

theorem PennyGraph.partial_family_three_boundary_le_five_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (hY : Y⊆G.defectPlaneFaces ht) :
    3*((G.familyUnpairedPorts Y).card : ℤ)≤5*G.familyK Y := by
  have hcount := G.partial_family_endpoint_conservation ht Y
  have hB : (G.familyUnpairedPorts Y).card≤(G.familyTrackComponents Y).card := by
    rw [G.familyUnpairedPorts_card Y]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hL : 5*Y.card≤(G.familySourcePorts Y).card := by
    rw [G.familySourcePorts_card Y]
    calc
      _ = ∑ _∈Y, 5 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun F hF => G.defect_source_ports_five_le ht F (hY hF))
  unfold familyK
  omega

end Swanepoel
