module
public import Swanepoel.L38BankFamilies
public import Swanepoel.JoinClosedDecomposition
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.familyUnpairedPort_unique {n : ℕ} (G : PennyGraph n)
    (Z : Finset (PlaneFace G)) (e : OrientedEdge G) (he : e∈G.familyUnpairedPorts Z)
    (f : OrientedEdge G) (hf : f∈G.familySourcePorts Z)
    (hc : edgeComponent f=edgeComponent e) : f=e := by
  have he' := Finset.mem_filter.mp he
  have hone := (Finset.mem_filter.mp he'.2).2
  apply Finset.card_le_one.mp hone.le
  · exact Finset.mem_filter.mpr ⟨hf,hc⟩
  · exact Finset.mem_filter.mpr ⟨he'.1,rfl⟩

theorem PennyGraph.familyUnpairedPort_of_subset {n : ℕ} (G : PennyGraph n)
    {Y Z : Finset (PlaneFace G)} (hYZ : Y⊆Z) (e : OrientedEdge G)
    (heY : e∈G.familySourcePorts Y) (heZ : e∈G.familyUnpairedPorts Z) :
    e∈G.familyUnpairedPorts Y := by
  have hec : edgeComponent e∈G.familyTrackComponents Y := Finset.mem_image.mpr ⟨e,heY,rfl⟩
  refine Finset.mem_filter.mpr ⟨heY,Finset.mem_filter.mpr ⟨hec,?_⟩⟩
  apply Finset.card_eq_one.mpr
  refine ⟨e,?_⟩
  ext f
  constructor
  · intro hf
    have hf' := Finset.mem_filter.mp hf
    have hfp := (Finset.mem_filter.mp hf'.1).2
    have hfZ : f∈G.familySourcePorts Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfp.1,hYZ hfp.2⟩
    exact Finset.mem_singleton.mpr (G.familyUnpairedPort_unique Z e heZ f hfZ hf'.2)
  · intro hf
    rw [Finset.mem_singleton.mp hf]
    exact Finset.mem_filter.mpr ⟨heY,rfl⟩

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def isolatedTwoPortPentagons (ht : G.TriangleFree) (side : Bool) : Finset (PlaneFace G) :=
  (B.bankDefectFamily ht side).filter (fun F =>
    (G.faceSourcePorts F).card=5 ∧ B.faceBankPortCount F=2 ∧
      ∀ e∈G.faceSourcePorts F,e∈G.familyUnpairedPorts (B.bankDefectFamily ht side))

def bankRemainder (ht : G.TriangleFree) (side : Bool) : Finset (PlaneFace G) :=
  B.bankDefectFamily ht side\B.isolatedTwoPortPentagons ht side

theorem bankRemainder_subset (ht : G.TriangleFree) (side : Bool) :
    B.bankRemainder ht side⊆B.bankDefectFamily ht side := Finset.sdiff_subset

theorem bank_isolated_remainder_disjoint (ht : G.TriangleFree) (side : Bool) :
    Disjoint (B.isolatedTwoPortPentagons ht side) (B.bankRemainder ht side) := by
  apply Finset.disjoint_left.mpr
  intro F hF hrest
  exact (Finset.mem_sdiff.mp hrest).2 hF

theorem bank_isolated_remainder_union (ht : G.TriangleFree) (side : Bool) :
    B.isolatedTwoPortPentagons ht side∪B.bankRemainder ht side=B.bankDefectFamily ht side :=
  Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

theorem isolated_sourcePorts_subset_unpaired (ht : G.TriangleFree) (side : Bool) :
    G.familySourcePorts (B.isolatedTwoPortPentagons ht side)⊆
      G.familyUnpairedPorts (B.bankDefectFamily ht side) := by
  intro e he
  have hep := (Finset.mem_filter.mp he).2
  have hiso := (Finset.mem_filter.mp hep.2).2
  exact hiso.2.2 e (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,rfl⟩)

theorem isolated_track_count (ht : G.TriangleFree) (side : Bool) :
    (G.familyTrackComponents (B.isolatedTwoPortPentagons ht side)).card=
      5*(B.isolatedTwoPortPentagons ht side).card := by
  have hinj := (G.familyUnpairedPorts_component_injOn (B.bankDefectFamily ht side)).mono
    (B.isolated_sourcePorts_subset_unpaired ht side)
  rw [PennyGraph.familyTrackComponents,Finset.card_image_of_injOn hinj,G.familySourcePorts_card]
  calc
    _ = ∑ _∈B.isolatedTwoPortPentagons ht side,5 := by
      apply Finset.sum_congr rfl
      intro F hF
      exact (Finset.mem_filter.mp hF).2.1
    _ = _ := by simp [Nat.mul_comm]

theorem isolated_remainder_tracks_disjoint (ht : G.TriangleFree) (side : Bool) :
    Disjoint (G.familyTrackComponents (B.isolatedTwoPortPentagons ht side))
      (G.familyTrackComponents (B.bankRemainder ht side)) := by
  apply Finset.disjoint_left.mpr
  intro c hcS hcY
  obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hcS
  obtain ⟨f,hf,hfc⟩ := Finset.mem_image.mp hcY
  have hfp := (Finset.mem_filter.mp hf).2
  have hfZ : f∈G.familySourcePorts (B.bankDefectFamily ht side) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfp.1,B.bankRemainder_subset ht side hfp.2⟩
  have hfe := G.familyUnpairedPort_unique (B.bankDefectFamily ht side) e
    (B.isolated_sourcePorts_subset_unpaired ht side he) f hfZ (hfc.trans hec.symm)
  have heS := (Finset.mem_filter.mp he).2.2
  exact (Finset.mem_sdiff.mp hfp.2).2 (hfe ▸ heS)

theorem remainder_unpaired_iff (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge G) (he : e∈G.familySourcePorts (B.bankRemainder ht side)) :
    e∈G.familyUnpairedPorts (B.bankRemainder ht side) ↔
      e∈G.familyUnpairedPorts (B.bankDefectFamily ht side) := by
  constructor
  · intro hfree
    have hep := (Finset.mem_filter.mp he).2
    have heZ : e∈G.familySourcePorts (B.bankDefectFamily ht side) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,B.bankRemainder_subset ht side hep.2⟩
    have hc : edgeComponent e∈G.familyTrackComponents (B.bankDefectFamily ht side) :=
      Finset.mem_image.mpr ⟨e,heZ,rfl⟩
    refine Finset.mem_filter.mpr ⟨heZ,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
    apply Finset.card_eq_one.mpr
    refine ⟨e,?_⟩
    ext f
    constructor
    · intro hf
      have hfp := Finset.mem_filter.mp hf
      have hfs := (Finset.mem_filter.mp hfp.1).2
      by_cases hiso : G.sourceFace f∈B.isolatedTwoPortPentagons ht side
      · have hfS : f∈G.familySourcePorts (B.isolatedTwoPortPentagons ht side) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfs.1,hiso⟩
        exact Finset.mem_singleton.mpr (G.familyUnpairedPort_unique (B.bankDefectFamily ht side)
          f (B.isolated_sourcePorts_subset_unpaired ht side hfS) e heZ hfp.2.symm).symm
      · have hfY : f∈G.familySourcePorts (B.bankRemainder ht side) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfs.1,Finset.mem_sdiff.mpr ⟨hfs.2,hiso⟩⟩
        exact Finset.mem_singleton.mpr (G.familyUnpairedPort_unique (B.bankRemainder ht side)
          e hfree f hfY hfp.2)
    · intro hf
      rw [Finset.mem_singleton.mp hf]
      exact Finset.mem_filter.mpr ⟨heZ,rfl⟩
  · exact G.familyUnpairedPort_of_subset (B.bankRemainder_subset ht side) e he

theorem remainder_two_crossing_pentagon_has_join (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankRemainder ht side)
    (hfive : (G.faceSourcePorts F).card=5) (htwo : B.faceBankPortCount F=2) :
    ∃ e∈G.faceSourcePorts F,edgeComponent e∈G.partialInternalJoins (B.bankRemainder ht side) := by
  by_contra hnot
  push Not at hnot
  have hall : ∀ e∈G.faceSourcePorts F,
      e∈G.familyUnpairedPorts (B.bankDefectFamily ht side) := by
    intro e he
    have hep := (Finset.mem_filter.mp he).2
    have heY : e∈G.familySourcePorts (B.bankRemainder ht side) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,hep.2 ▸ hF⟩
    have hc : edgeComponent e∈G.familyTrackComponents (B.bankRemainder ht side) :=
      Finset.mem_image.mpr ⟨e,heY,rfl⟩
    have hfree : edgeComponent e∈G.familyUnpairedTracks (B.bankRemainder ht side) := by
      by_contra hn
      exact hnot e he (Finset.mem_sdiff.mpr ⟨hc,hn⟩)
    exact (B.remainder_unpaired_iff ht side e heY).mp (Finset.mem_filter.mpr ⟨heY,hfree⟩)
  have hiso : F∈B.isolatedTwoPortPentagons ht side :=
    Finset.mem_filter.mpr ⟨B.bankRemainder_subset ht side hF,hfive,htwo,hall⟩
  exact (Finset.mem_sdiff.mp hF).2 hiso

theorem bank_partition_counts (ht : G.TriangleFree) (side : Bool) :
    (B.subfamilyMeetingPorts (B.bankDefectFamily ht side)).card=
        2*(B.isolatedTwoPortPentagons ht side).card+
          (B.subfamilyMeetingPorts (B.bankRemainder ht side)).card ∧
    G.familyK (B.bankDefectFamily ht side)=
        3*(B.isolatedTwoPortPentagons ht side).card+G.familyK (B.bankRemainder ht side) ∧
    G.familyPortExcess (B.bankDefectFamily ht side)=
        (B.isolatedTwoPortPentagons ht side).card+G.familyPortExcess (B.bankRemainder ht side) := by
  have hU := B.bank_isolated_remainder_union ht side
  have hDis := B.bank_isolated_remainder_disjoint ht side
  have hFace := Finset.card_union_of_disjoint hDis
  rw [hU] at hFace
  have hTracks := Finset.card_union_of_disjoint (B.isolated_remainder_tracks_disjoint ht side)
  rw [← G.familyTrackComponents_union,hU,B.isolated_track_count ht side] at hTracks
  have hD : (B.subfamilyMeetingPorts (B.bankDefectFamily ht side)).card=
      2*(B.isolatedTwoPortPentagons ht side).card+
        (B.subfamilyMeetingPorts (B.bankRemainder ht side)).card := by
    rw [B.subfamilyMeetingPorts_card_eq_sum,← hU,Finset.sum_union hDis]
    rw [← B.subfamilyMeetingPorts_card_eq_sum (B.bankRemainder ht side)]
    congr 1
    calc
      _ = ∑ _∈B.isolatedTwoPortPentagons ht side,2 := by
        apply Finset.sum_congr rfl
        intro F hF
        exact (Finset.mem_filter.mp hF).2.2.1
      _ = _ := by simp [Nat.mul_comm]
  have hK : G.familyK (B.bankDefectFamily ht side)=
      3*(B.isolatedTwoPortPentagons ht side).card+G.familyK (B.bankRemainder ht side) := by
    have hTracksZ : ((G.familyTrackComponents (B.bankDefectFamily ht side)).card : ℤ)=
        5*(B.isolatedTwoPortPentagons ht side).card+
          (G.familyTrackComponents (B.bankRemainder ht side)).card := by exact_mod_cast hTracks
    have hFaceZ : ((B.bankDefectFamily ht side).card : ℤ)=
        (B.isolatedTwoPortPentagons ht side).card+(B.bankRemainder ht side).card := by exact_mod_cast hFace
    unfold PennyGraph.familyK
    omega
  refine ⟨hD,hK,?_⟩
  rw [← hU,G.familyPortExcess_union hDis]
  congr 1
  unfold PennyGraph.familyPortExcess
  calc
    _ = ∑ _∈B.isolatedTwoPortPentagons ht side,(1:ℤ) := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [(Finset.mem_filter.mp hF).2.1]
      norm_num
    _ = _ := by simp

end OrdinaryCutBanks
end Swanepoel
