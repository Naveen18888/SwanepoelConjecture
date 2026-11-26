module
public import Swanepoel.PartialFamilyPortCounts
public import Swanepoel.JoinClosedCrossings
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.familyCrossingDegree {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) (c : TrackComponent G) : ℕ :=
  (A.filter (fun a => ComponentCrosses a c)).card

theorem PennyGraph.interFamilyCrossings_eq_degree_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y Z : Finset (PlaneFace G)) :
    G.interFamilyCrossings ht Y Z=
      ∑ c∈G.familyTrackComponents Z,G.familyCrossingDegree (G.familyTrackComponents Y) c := by
  let E := Fintype.equivFin (TrackComponent G)
  let A := G.familyTrackComponents Y
  let B := G.familyTrackComponents Z
  have hcard : (((A.map E.toEmbedding).product (B.map E.toEmbedding)).filter
      (fun p => ComponentCrosses (E.symm p.1) (E.symm p.2))).card=
      ((A.product B).filter (fun p => ComponentCrosses p.1 p.2)).card := by
    apply Eq.symm
    refine Finset.card_bij (fun p _ => (E p.1,E p.2)) ?_ ?_ ?_
    · intro p hp
      have h := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_map.mpr ⟨p.1,(Finset.mem_product.mp h.1).1,rfl⟩,
          Finset.mem_map.mpr ⟨p.2,(Finset.mem_product.mp h.1).2,rfl⟩⟩,by simpa using h.2⟩
    · intro p _ q _ h
      exact Prod.ext (E.injective (congrArg Prod.fst h)) (E.injective (congrArg Prod.snd h))
    · intro p hp
      have h := Finset.mem_filter.mp hp
      obtain ⟨a,ha,hea⟩ := Finset.mem_map.mp (Finset.mem_product.mp h.1).1
      obtain ⟨b,hb,heb⟩ := Finset.mem_map.mp (Finset.mem_product.mp h.1).2
      refine ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,?_⟩,Prod.ext hea heb⟩
      have hea' : E a=p.1 := hea
      have heb' : E b=p.2 := heb
      simpa only [← hea',← heb',Equiv.symm_apply_apply] using h.2
  change (((A.map E.toEmbedding).product (B.map E.toEmbedding)).filter
    (fun p => ComponentCrosses (E.symm p.1) (E.symm p.2))).card=_
  rw [hcard]
  simp only [PennyGraph.familyCrossingDegree,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.product_eq_sprod,Finset.sum_product]
  exact Finset.sum_comm

theorem PennyGraph.join_port_fiber_card_two {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Z : Finset (PlaneFace G)} (hZ : G.IsJoinClosed ht Z)
    (c : TrackComponent G) (hc : c∈G.familyJoinTrackComponents Z) :
    (G.familyPortFiber Z c).card=2 := by
  have hall := ((G.familyJoin_iff_all_ends_in_family ht hZ c).mp hc).2
  have heq : G.familyPortFiber Z c=Finset.univ.filter (fun e => SpineSource e ∧ edgeComponent e=c) := by
    ext e
    simp only [PennyGraph.familyPortFiber,PennyGraph.familySourcePorts,Finset.mem_filter,
      Finset.mem_univ,true_and]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hall e h.1 h.2⟩,h.2⟩⟩
  rw [heq,component_source_count ht c]

theorem PennyGraph.mixed_crossings_add_joins_le_slots {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) {Z : Finset (PlaneFace G)}
    (hZ : G.IsJoinClosed ht Z) (slot : OrientedEdge G→ℕ)
    (hcapacity : ∀ e∈G.familySourcePorts Z,
      G.familyCrossingDegree (G.familyTrackComponents Y) (edgeComponent e)≤slot e)
    (hsilent : ∀ c∈G.familyJoinTrackComponents Z,
      G.familyCrossingDegree (G.familyTrackComponents Y) c=0 →
        1≤∑ e∈G.familyPortFiber Z c,slot e) :
    G.interFamilyCrossings ht Y Z+G.familyJoinCount Z≤∑ e∈G.familySourcePorts Z,slot e := by
  have hlocal (c : TrackComponent G) (hc : c∈G.familyTrackComponents Z) :
      G.familyCrossingDegree (G.familyTrackComponents Y) c+(if c∈G.familyJoinTrackComponents Z then 1 else 0)≤
        ∑ e∈G.familyPortFiber Z c,slot e := by
    have hcap (e : OrientedEdge G) (he : e∈G.familyPortFiber Z c) :
        G.familyCrossingDegree (G.familyTrackComponents Y) c≤slot e := by
      have h := hcapacity e (Finset.mem_filter.mp he).1
      rwa [(Finset.mem_filter.mp he).2] at h
    by_cases hj : c∈G.familyJoinTrackComponents Z
    · rw [ite_eq_left hj]
      by_cases hz : G.familyCrossingDegree (G.familyTrackComponents Y) c=0
      · simpa only [hz,zero_add] using hsilent c hj hz
      have hsum : 2*G.familyCrossingDegree (G.familyTrackComponents Y) c≤∑ e∈G.familyPortFiber Z c,slot e := by
        calc
          _ = ∑ _∈G.familyPortFiber Z c,G.familyCrossingDegree (G.familyTrackComponents Y) c := by
            simp [G.join_port_fiber_card_two ht hZ c hj]
          _ ≤ _ := Finset.sum_le_sum hcap
      omega
    · rw [ite_eq_right hj,add_zero]
      obtain ⟨e,he⟩ := (G.familyPortFiber_nonempty_iff Z c).mpr hc
      exact (hcap e he).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) he)
  have hJsub : G.familyJoinTrackComponents Z⊆G.familyTrackComponents Z := Finset.sdiff_subset
  have hJ : (∑ c∈G.familyTrackComponents Z,if c∈G.familyJoinTrackComponents Z then 1 else 0)=G.familyJoinCount Z := by
    calc
      _ = ∑ c∈G.familyJoinTrackComponents Z,if c∈G.familyJoinTrackComponents Z then 1 else 0 :=
        (Finset.sum_subset hJsub (fun c _ hn => by rw [ite_eq_right hn])).symm
      _ = _ := by simp [PennyGraph.familyJoinCount]
  have hfib : (∑ c∈G.familyTrackComponents Z,∑ e∈G.familyPortFiber Z c,slot e)=
      ∑ e∈G.familySourcePorts Z,slot e :=
    Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_image.mpr ⟨e,he,rfl⟩) slot
  have hsum := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib,hJ,hfib,← G.interFamilyCrossings_eq_degree_sum ht Y Z] at hsum
  exact hsum

end Swanepoel
