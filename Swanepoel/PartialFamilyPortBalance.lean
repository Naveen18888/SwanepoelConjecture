module
public import Swanepoel.PartialFamilyPortCounts
public import Swanepoel.FaceBoundaryPermutation
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.family_source_normals_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (hY : Y⊆G.defectPlaneFaces ht) :
    (∑ e∈G.familySourcePorts Y,sourceNormal e)=0 := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun e he => (Finset.mem_filter.mp he).2.2 : ∀ e∈G.familySourcePorts Y,G.sourceFace e∈Y)
    sourceNormal]
  apply Finset.sum_eq_zero
  intro F hF
  have hf : (G.familySourcePorts Y).filter (fun e => G.sourceFace e=F)=G.faceSourcePorts F := by
    ext e
    simp only [PennyGraph.familySourcePorts,PennyGraph.faceSourcePorts,Finset.mem_filter,
      Finset.mem_univ,true_and]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2 ▸ hF⟩,h.2⟩⟩
  rw [hf]
  exact G.defect_all_source_normals_sum ht F (hY hF)

theorem PennyGraph.family_two_port_fiber_normals_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (c : TrackComponent G)
    (hcard : (G.familyPortFiber Y c).card=2) :
    (∑ e∈G.familyPortFiber Y c,sourceNormal e)=0 := by
  obtain ⟨e,f,hne,hpair⟩ := Finset.card_eq_two.mp hcard
  have he : e∈G.familyPortFiber Y c := by rw [hpair]; simp
  have hf : f∈G.familyPortFiber Y c := by rw [hpair]; simp
  have he' := Finset.mem_filter.mp he
  have hf' := Finset.mem_filter.mp hf
  have hn := source_normals_opposite ht (Finset.mem_filter.mp he'.1).2.1
    (Finset.mem_filter.mp hf'.1).2.1 (hf'.2.trans he'.2.symm) (Ne.symm hne)
  rw [hpair,Finset.sum_pair hne,hn,add_neg_cancel]

theorem PennyGraph.family_unpaired_normals_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) (hY : Y⊆G.defectPlaneFaces ht) :
    (∑ e∈G.familyUnpairedPorts Y,sourceNormal e)=0 := by
  have hS := Finset.sum_fiberwise_of_maps_to
    (fun e he => Finset.mem_image.mpr ⟨e,he,rfl⟩ :
      ∀ e∈G.familySourcePorts Y,edgeComponent e∈G.familyTrackComponents Y) sourceNormal
  have hQ := Finset.sum_fiberwise_of_maps_to
    (fun e he => Finset.mem_image.mpr ⟨e,(Finset.mem_filter.mp he).1,rfl⟩ :
      ∀ e∈G.familyUnpairedPorts Y,edgeComponent e∈G.familyTrackComponents Y) sourceNormal
  rw [← hQ]
  calc
    _ = ∑ c∈G.familyTrackComponents Y,∑ e∈G.familyPortFiber Y c,sourceNormal e := by
      apply Finset.sum_congr rfl
      intro c hc
      rcases G.familyPortFiber_card_one_or_two ht Y hc with hone | htwo
      · have hf : (G.familyUnpairedPorts Y).filter (fun e => edgeComponent e=c)=G.familyPortFiber Y c := by
          ext e
          constructor
          · intro he
            have he' := Finset.mem_filter.mp he
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he'.1).1,he'.2⟩
          · intro he
            have he' := Finset.mem_filter.mp he
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he'.1,?_⟩,he'.2⟩
            rw [he'.2]
            exact Finset.mem_filter.mpr ⟨hc,hone⟩
        rw [hf]
      · have hf : (G.familyUnpairedPorts Y).filter (fun e => edgeComponent e=c)=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro e he
          have he' := Finset.mem_filter.mp he
          have hm := (Finset.mem_filter.mp (Finset.mem_filter.mp he'.1).2).2
          rw [he'.2,htwo] at hm
          norm_num at hm
        rw [hf,Finset.sum_empty,G.family_two_port_fiber_normals_sum ht Y c htwo]
    _ = 0 := hS.trans (G.family_source_normals_sum ht Y hY)

end Swanepoel
