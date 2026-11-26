module
public import Swanepoel.PartialFamilyPortBalance
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem balanced_unit_subset_projection {ι : Type*} [DecidableEq ι]
    (Q P : Finset ι) (hPQ : P⊆Q) (normal : ι→Plane) (v : Plane) (α : ℝ)
    (hv : ‖v‖=1) (hnorm : ∀ i∈Q,‖normal i‖=1) (hsum : ∑ i∈Q,normal i=0)
    (hcone : ∀ i∈P,α ≤ inner ℝ v (normal i)) : (1+α)*(P.card : ℝ)≤Q.card := by
  have hP : α*(P.card : ℝ)≤∑ i∈P,inner ℝ v (normal i) := by
    calc
      _ = ∑ _∈P,α := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hcone
  have hO : -((Q\P).card : ℝ)≤∑ i∈Q\P,inner ℝ v (normal i) := by
    calc
      _ = ∑ _∈Q\P,(-1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (by
        intro i hi
        have hh := abs_real_inner_le_norm v (normal i)
        rw [hv,hnorm i (Finset.mem_sdiff.mp hi).1,mul_one] at hh
        exact (abs_le.mp hh).1)
  have hz : (∑ i∈Q,inner ℝ v (normal i))=0 := by
    rw [← inner_sum,hsum,inner_zero_right]
  have hp := Finset.sum_sdiff (f := fun i => inner ℝ v (normal i)) hPQ
  have hc : ((Q\P).card : ℝ)+P.card=Q.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hPQ
  linarith

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def bankBoundaryPorts (ht : G.TriangleFree) (side : Bool) : Finset (OrientedEdge G) :=
  G.familyUnpairedPorts (B.bankDefectFamily ht side)

def bankMeetingPorts (ht : G.TriangleFree) (side : Bool) : Finset (OrientedEdge G) :=
  (G.familySourcePorts (B.bankDefectFamily ht side)).filter
    (fun e => ComponentCrosses cut (edgeComponent e))

theorem bankMeetingPorts_component_injOn (ht : G.TriangleFree) (side : Bool) :
    Set.InjOn edgeComponent (B.bankMeetingPorts ht side : Set (OrientedEdge G)) := by
  intro e he f hf hc
  have he' := Finset.mem_filter.mp he
  have hf' := Finset.mem_filter.mp hf
  have heS := (Finset.mem_filter.mp he'.1).2
  have hfS := (Finset.mem_filter.mp hf'.1).2
  exact B.crossing_bank_sources_eq ht side e f heS.1 hfS.1 heS.2 hfS.2 hc.symm
    ((componentGraph G ht).adj_symm he'.2)

theorem bankMeetingPorts_image (ht : G.TriangleFree) (side : Bool) :
    (B.bankMeetingPorts ht side).image edgeComponent=B.bankMeetingAnchors ht side := by
  ext c
  constructor
  · intro hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e,he'.1,rfl⟩,he'.2⟩
  · intro hc
    have hc' := Finset.mem_filter.mp hc
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hc'.1
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hec ▸ hc'.2⟩,hec⟩

theorem bankMeetingPorts_card (ht : G.TriangleFree) (side : Bool) :
    (B.bankMeetingPorts ht side).card=(B.bankMeetingAnchors ht side).card := by
  rw [← B.bankMeetingPorts_image ht side,
    Finset.card_image_of_injOn (B.bankMeetingPorts_component_injOn ht side)]

theorem bankMeetingPorts_subset_boundary (ht : G.TriangleFree) (side : Bool) :
    B.bankMeetingPorts ht side⊆B.bankBoundaryPorts ht side := by
  intro e he
  have he' := Finset.mem_filter.mp he
  have heS := (Finset.mem_filter.mp he'.1).2
  have hc : edgeComponent e∈G.familyTrackComponents (B.bankDefectFamily ht side) :=
    Finset.mem_image.mpr ⟨e,he'.1,rfl⟩
  refine Finset.mem_filter.mpr ⟨he'.1,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
  apply Finset.card_eq_one.mpr
  refine ⟨e,?_⟩
  ext f
  constructor
  · intro hf
    have hf' := Finset.mem_filter.mp hf
    have hfS := (Finset.mem_filter.mp hf'.1).2
    exact Finset.mem_singleton.mpr (B.crossing_bank_sources_eq ht side e f
      heS.1 hfS.1 heS.2 hfS.2 hf'.2 ((componentGraph G ht).adj_symm he'.2)).symm
  · intro hf
    rw [Finset.mem_singleton.mp hf]
    exact Finset.mem_filter.mpr ⟨he'.1,rfl⟩

theorem bankBoundaryPorts_normal_sum (ht : G.TriangleFree) (side : Bool) :
    (∑ e∈B.bankBoundaryPorts ht side,sourceNormal e)=0 :=
  G.family_unpaired_normals_sum ht _ (Finset.filter_subset _ _)

theorem bank_boundary_cone_bound (ht : G.TriangleFree) (side : Bool) :
    (1+Real.sqrt 3/2)*((B.bankMeetingAnchors ht side).card : ℝ)≤
      (B.bankBoundaryPorts ht side).card := by
  rw [← B.bankMeetingPorts_card ht side]
  apply balanced_unit_subset_projection (B.bankBoundaryPorts ht side) (B.bankMeetingPorts ht side)
    (B.bankMeetingPorts_subset_boundary ht side) sourceNormal (B.signedVector side) (Real.sqrt 3/2)
    (B.signedVector_norm side) (fun e _ => sourceNormal_norm e) (B.bankBoundaryPorts_normal_sum ht side)
  intro e he
  have he' := Finset.mem_filter.mp he
  have heS := (Finset.mem_filter.mp he'.1).2
  have hcone := B.crossing_signed_normal_cone ht e heS.1 (Finset.mem_filter.mp heS.2).1
    ((componentGraph G ht).adj_symm he'.2)
  rw [(Finset.mem_filter.mp heS.2).2] at hcone
  exact hcone.le

end OrdinaryCutBanks
end Swanepoel
