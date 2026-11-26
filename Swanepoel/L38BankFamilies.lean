module
public import Swanepoel.BankBound
public import Swanepoel.PentagonConeAccounting
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.partialInternalJoins {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) : Finset (TrackComponent G) :=
  G.familyTrackComponents Y\G.familyUnpairedTracks Y

theorem PennyGraph.partial_tracks_boundary_add_joins {n : ℕ} (G : PennyGraph n)
    (Y : Finset (PlaneFace G)) :
    (G.familyTrackComponents Y).card=(G.familyUnpairedPorts Y).card+(G.partialInternalJoins Y).card := by
  rw [G.familyUnpairedPorts_card Y]
  have hsub : G.familyUnpairedTracks Y⊆G.familyTrackComponents Y := Finset.filter_subset _ _
  have h := Finset.card_sdiff_add_card_eq_card hsub
  dsimp [PennyGraph.partialInternalJoins]
  omega

theorem PennyGraph.partial_internal_join_fiber_card {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (c : TrackComponent G)
    (hc : c∈G.partialInternalJoins Y) : (G.familyPortFiber Y c).card=2 := by
  have hh := Finset.mem_sdiff.mp hc
  rcases G.familyPortFiber_card_one_or_two ht Y hh.1 with h | h
  · exact False.elim (hh.2 (Finset.mem_filter.mpr ⟨hh.1,h⟩))
  · exact h

theorem PennyGraph.partial_family_bank_identities {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) :
    ((G.familySourcePorts Y).card : ℤ)=4*Y.card+G.familyPortExcess Y ∧
    2*G.familyK Y=(G.familyUnpairedPorts Y).card+G.familyPortExcess Y ∧
    G.familyK Y=2*Y.card+G.familyPortExcess Y-(G.partialInternalJoins Y).card := by
  have hp : ((G.familySourcePorts Y).card : ℤ)=∑ F∈Y,((G.faceSourcePorts F).card : ℤ) := by
    exact_mod_cast G.familySourcePorts_card Y
  have hex := G.familyPortExcess_eq Y
  have hc := G.partial_tracks_boundary_add_joins Y
  have hcZ : ((G.familyTrackComponents Y).card : ℤ)=
      (G.familyUnpairedPorts Y).card+(G.partialInternalJoins Y).card := by exact_mod_cast hc
  have hk := G.partial_family_K_port_conservation ht Y
  refine ⟨by omega,hk,?_⟩
  unfold PennyGraph.familyK at hk ⊢
  omega

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def subfamilyMeetingPorts (_B : OrdinaryCutBanks G cut) (Y : Finset (PlaneFace G)) : Finset (OrientedEdge G) :=
  (G.familySourcePorts Y).filter (fun e => ComponentCrosses cut (edgeComponent e))

def subfamilyMeetingTracks (Y : Finset (PlaneFace G)) : Finset (TrackComponent G) :=
  (B.subfamilyMeetingPorts Y).image edgeComponent

def faceBankPortCount (_B : OrdinaryCutBanks G cut) (F : PlaneFace G) : ℕ :=
  ((G.faceSourcePorts F).filter (fun e => ComponentCrosses cut (edgeComponent e))).card

theorem subfamilyMeetingPorts_subset (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    B.subfamilyMeetingPorts Y⊆B.bankMeetingPorts ht side := by
  intro e he
  have he' := Finset.mem_filter.mp he
  have hp := (Finset.mem_filter.mp he'.1).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1,hY hp.2⟩,he'.2⟩

theorem subfamilyMeetingPorts_component_injOn (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    Set.InjOn edgeComponent (B.subfamilyMeetingPorts Y : Set (OrientedEdge G)) := by
  intro e he f hf hc
  exact B.bankMeetingPorts_component_injOn ht side
    (B.subfamilyMeetingPorts_subset ht side Y hY he)
    (B.subfamilyMeetingPorts_subset ht side Y hY hf) hc

theorem subfamilyMeetingTracks_card (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.subfamilyMeetingTracks Y).card=(B.subfamilyMeetingPorts Y).card :=
  Finset.card_image_of_injOn (B.subfamilyMeetingPorts_component_injOn ht side Y hY)

theorem subfamilyMeetingPorts_subset_unpaired (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    B.subfamilyMeetingPorts Y⊆G.familyUnpairedPorts Y := by
  intro e he
  have he' := Finset.mem_filter.mp he
  have hp := (Finset.mem_filter.mp he'.1).2
  have hc : edgeComponent e∈G.familyTrackComponents Y := Finset.mem_image.mpr ⟨e,he'.1,rfl⟩
  refine Finset.mem_filter.mpr ⟨he'.1,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
  apply Finset.card_eq_one.mpr
  refine ⟨e,?_⟩
  ext f
  constructor
  · intro hf
    have hf' := Finset.mem_filter.mp hf
    have hfp := (Finset.mem_filter.mp hf'.1).2
    apply Finset.mem_singleton.mpr
    exact (B.crossing_bank_sources_eq ht side e f hp.1 hfp.1 (hY hp.2) (hY hfp.2)
      hf'.2 ((componentGraph G ht).adj_symm he'.2)).symm
  · intro hf
    rw [Finset.mem_singleton.mp hf]
    exact Finset.mem_filter.mpr ⟨he'.1,rfl⟩

theorem subfamily_boundary_cone_bound (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (1+Real.sqrt 3/2)*((B.subfamilyMeetingPorts Y).card : ℝ)≤(G.familyUnpairedPorts Y).card := by
  apply balanced_unit_subset_projection (G.familyUnpairedPorts Y) (B.subfamilyMeetingPorts Y)
    (B.subfamilyMeetingPorts_subset_unpaired ht side Y hY) sourceNormal (B.signedVector side) (Real.sqrt 3/2)
    (B.signedVector_norm side) (fun e _ => sourceNormal_norm e)
    (G.family_unpaired_normals_sum ht Y (hY.trans (Finset.filter_subset _ _)))
  intro e he
  have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have heY := hY hp.2
  have hc := B.crossing_signed_normal_cone ht e hp.1 (Finset.mem_filter.mp heY).1
    ((componentGraph G ht).adj_symm (Finset.mem_filter.mp he).2)
  rw [(Finset.mem_filter.mp heY).2] at hc
  exact hc.le

theorem subfamily_restriction_five (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    9*((B.subfamilyMeetingPorts Y).card : ℤ)≤10*G.familyK Y-5*G.familyPortExcess Y := by
  have hcone := B.subfamily_boundary_cone_bound ht side Y hY
  have hs : (8/5:ℝ)≤Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3:ℝ),Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  have hscale := mul_nonneg (sub_nonneg.mpr hs)
    (Nat.cast_nonneg (B.subfamilyMeetingPorts Y).card : (0:ℝ)≤_)
  have hreal : (9:ℝ)*(B.subfamilyMeetingPorts Y).card≤5*(G.familyUnpairedPorts Y).card := by
    nlinarith only [hcone,hscale]
  have hz : 9*((B.subfamilyMeetingPorts Y).card : ℤ)≤5*(G.familyUnpairedPorts Y).card := by exact_mod_cast hreal
  have hk := G.partial_family_K_port_conservation ht Y
  omega

theorem subfamilyMeetingPorts_card_eq_sum (Y : Finset (PlaneFace G)) :
    (B.subfamilyMeetingPorts Y).card=∑ F∈Y,B.faceBankPortCount F := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := G.sourceFace)
    (s := B.subfamilyMeetingPorts Y) (t := Y)
    (fun e he => (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2)
  rw [hfib]
  apply Finset.sum_congr rfl
  intro F hF
  congr 1
  ext e
  simp only [subfamilyMeetingPorts,PennyGraph.familySourcePorts,PennyGraph.faceSourcePorts,
    Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => ⟨⟨h.1.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨⟨h.1.1,h.1.2 ▸ hF⟩,h.2⟩,h.1.2⟩⟩

end OrdinaryCutBanks
end Swanepoel
