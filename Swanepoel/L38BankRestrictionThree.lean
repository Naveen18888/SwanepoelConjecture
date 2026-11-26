module
public import Swanepoel.L38BankCones
public import Swanepoel.L38BankPartition
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def twoCrossingPentagons (Y : Finset (PlaneFace G)) : Finset (PlaneFace G) :=
  Y.filter (fun F => (G.faceSourcePorts F).card=5 ∧ B.faceBankPortCount F=2)

def pentagonJoinPorts (Y : Finset (PlaneFace G)) : Finset (OrientedEdge G) :=
  (G.familySourcePorts (B.twoCrossingPentagons Y)).filter
    (fun e => edgeComponent e∈G.partialInternalJoins Y)

theorem face_crossing_slots_lower (Y : Finset (PlaneFace G)) (F : PlaneFace G) (hF : F∈Y)
    (axis : Bool→Plane)
    (hcross : ∀ e∈B.subfamilyMeetingPorts Y,twoConeSlots axis (sourceNormal e)=2) :
    2*B.faceBankPortCount F≤∑ e∈G.faceSourcePorts F,twoConeSlots axis (sourceNormal e) := by
  let P := (G.faceSourcePorts F).filter (fun e => ComponentCrosses cut (edgeComponent e))
  have hs : (∑ e∈P,twoConeSlots axis (sourceNormal e))=∑ _∈P,2 := by
    apply Finset.sum_congr rfl
    intro e he
    have hp := Finset.mem_filter.mp he
    have hep := (Finset.mem_filter.mp hp.1).2
    exact hcross e (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,hep.2 ▸ hF⟩,hp.2⟩)
  calc
    _ = ∑ e∈P,twoConeSlots axis (sourceNormal e) := by
      rw [hs]
      simp [P,faceBankPortCount,Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

theorem two_crossing_pentagon_join_slots_zero (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side)
    (axis : Bool→Plane) (hnorm : ∀ b,‖axis b‖=1)
    (hcross : ∀ e∈B.subfamilyMeetingPorts Y,twoConeSlots axis (sourceNormal e)=2)
    (e : OrientedEdge G) (he : e∈B.pentagonJoinPorts Y) :
    twoConeSlots axis (sourceNormal e)=0 := by
  have he' := Finset.mem_filter.mp he
  have hep := (Finset.mem_filter.mp he'.1).2
  have hbad := Finset.mem_filter.mp hep.2
  let F := G.sourceFace e
  have heF : e∈G.faceSourcePorts F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,rfl⟩
  let P := (G.faceSourcePorts F).filter (fun f => ComponentCrosses cut (edgeComponent f))
  have heP : e∉P := by
    intro h
    have heY : e∈G.familySourcePorts Y := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,hbad.1⟩
    have hmeet : e∈B.subfamilyMeetingPorts Y := Finset.mem_filter.mpr ⟨heY,(Finset.mem_filter.mp h).2⟩
    have hfree := (Finset.mem_filter.mp (B.subfamilyMeetingPorts_subset_unpaired ht side Y hY hmeet)).2
    exact (Finset.mem_sdiff.mp he'.2).2 hfree
  have hP : P.card=2 := hbad.2.2
  have hsumP : (∑ f∈P,twoConeSlots axis (sourceNormal f))=4 := by
    calc
      _ = ∑ _∈P,2 := by
        apply Finset.sum_congr rfl
        intro f hf
        have hfp := Finset.mem_filter.mp hf
        have hfs := (Finset.mem_filter.mp hfp.1).2
        exact hcross f (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfs.1,hfs.2 ▸ hbad.1⟩,hfp.2⟩)
      _ = _ := by simp [hP]
  have hslot : 4+twoConeSlots axis (sourceNormal e)≤
      ∑ f∈G.faceSourcePorts F,twoConeSlots axis (sourceNormal f) := by
    calc
      _ = ∑ f∈insert e P,twoConeSlots axis (sourceNormal f) := by
        rw [Finset.sum_insert heP,hsumP]
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.insert_subset heF (Finset.filter_subset _ _)) (fun _ _ _ => Nat.zero_le _)
  have hface := G.two_cone_slots_face_bound ht F (Finset.mem_filter.mp (hY hbad.1)).1 hdegree axis hnorm
  rw [hbad.2.1] at hface
  omega

theorem pentagonJoinPorts_component_injOn (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    Set.InjOn edgeComponent (B.pentagonJoinPorts Y : Set (OrientedEdge G)) := by
  obtain ⟨axis,hnorm,hsep,hcross⟩ := B.subfamily_two_cone_axes ht side Y hY
  intro e he f hf hc
  by_contra hne
  have he0 := B.two_crossing_pentagon_join_slots_zero ht side hdegree Y hY axis hnorm hcross e he
  have hf0 := B.two_crossing_pentagon_join_slots_zero ht side hdegree Y hY axis hnorm hcross f hf
  have hes := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.1
  have hfs := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2.1
  have hopp := source_normals_opposite ht hes hfs hc.symm (Ne.symm hne)
  have hcover := twoConeSlots_antipodal_cover axis (sourceNormal e) hnorm (sourceNormal_norm e) hsep
  rw [← hopp,he0,hf0] at hcover
  omega

theorem remainder_two_crossing_pentagons_le_joins (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a) :
    (B.twoCrossingPentagons (B.bankRemainder ht side)).card≤
      (G.partialInternalJoins (B.bankRemainder ht side)).card := by
  let Y := B.bankRemainder ht side
  let P := B.pentagonJoinPorts Y
  have hfaces : B.twoCrossingPentagons Y⊆P.image G.sourceFace := by
    intro F hF
    have hbad := Finset.mem_filter.mp hF
    obtain ⟨e,he,hjoin⟩ := B.remainder_two_crossing_pentagon_has_join ht side F hbad.1 hbad.2.1 hbad.2.2
    have hep := (Finset.mem_filter.mp he).2
    refine Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨?_,hjoin⟩,hep.2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,hep.2 ▸ hF⟩
  have hjoin : P.image edgeComponent⊆G.partialInternalJoins Y := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp he).2
  calc
    _ ≤ (P.image G.sourceFace).card := Finset.card_le_card hfaces
    _ ≤ P.card := Finset.card_image_le
    _ = (P.image edgeComponent).card :=
      (Finset.card_image_of_injOn (B.pentagonJoinPorts_component_injOn ht side hdegree Y
        (B.bankRemainder_subset ht side))).symm
    _ ≤ _ := Finset.card_le_card hjoin

theorem subfamily_face_crossings_bound (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side)
    (F : PlaneFace G) (hF : F∈Y) :
    (B.faceBankPortCount F : ℤ)≤3*(G.faceSourcePorts F).card-14+
      (if F∈B.twoCrossingPentagons Y then 1 else 0) := by
  obtain ⟨axis,hnorm,hsep,hcross⟩ := B.subfamily_two_cone_axes ht side Y hY
  have hlo := B.face_crossing_slots_lower Y F hF axis hcross
  have hhi := G.two_cone_slots_face_bound ht F (Finset.mem_filter.mp (hY hF)).1 hdegree axis hnorm
  have hm := G.defect_source_ports_five_le ht F (Finset.mem_filter.mp (hY hF)).1
  have hcount : B.faceBankPortCount F+3≤(G.faceSourcePorts F).card := by omega
  by_cases hbad : F∈B.twoCrossingPentagons Y
  · rw [ite_eq_left hbad]
    have hb := (Finset.mem_filter.mp hbad).2
    rw [hb.1,hb.2]
    norm_num
  · rw [ite_eq_right hbad]
    have hn : ¬ ((G.faceSourcePorts F).card=5 ∧ B.faceBankPortCount F=2) := by
      intro h
      exact hbad (Finset.mem_filter.mpr ⟨hF,h⟩)
    omega

theorem remainder_restriction_three (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a) :
    ((B.subfamilyMeetingPorts (B.bankRemainder ht side)).card : ℤ)≤
      4*G.familyPortExcess (B.bankRemainder ht side)-G.familyK (B.bankRemainder ht side) := by
  let Y := B.bankRemainder ht side
  have hsum := Finset.sum_le_sum (B.subfamily_face_crossings_bound ht side hdegree Y
    (B.bankRemainder_subset ht side))
  have hIndicator : (∑ F∈Y,if F∈B.twoCrossingPentagons Y then (1:ℤ) else 0)=
      (B.twoCrossingPentagons Y).card := by
    have hsub : B.twoCrossingPentagons Y⊆Y := Finset.filter_subset _ _
    calc
      _ = ∑ F∈B.twoCrossingPentagons Y,if F∈B.twoCrossingPentagons Y then (1:ℤ) else 0 :=
        (Finset.sum_subset hsub (fun F _ hn => by rw [ite_eq_right hn])).symm
      _ = _ := by simp
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hIndicator] at hsum
  simp only [Finset.sum_const,Int.nsmul_eq_mul] at hsum
  have hD : ((B.subfamilyMeetingPorts Y).card : ℤ)=∑ F∈Y,(B.faceBankPortCount F : ℤ) := by
    exact_mod_cast B.subfamilyMeetingPorts_card_eq_sum Y
  have hL : ((G.familySourcePorts Y).card : ℤ)=∑ F∈Y,((G.faceSourcePorts F).card : ℤ) := by
    exact_mod_cast G.familySourcePorts_card Y
  have hJ : ((B.twoCrossingPentagons Y).card : ℤ)≤(G.partialInternalJoins Y).card := by
    exact_mod_cast B.remainder_two_crossing_pentagons_le_joins ht side hdegree
  have hid := G.partial_family_bank_identities ht Y
  change ((B.subfamilyMeetingPorts Y).card : ℤ)≤4*G.familyPortExcess Y-G.familyK Y
  omega

end OrdinaryCutBanks
end Swanepoel
