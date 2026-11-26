module
public import Swanepoel.L38HalfPentagonTracks
public import Swanepoel.L38HalfAreaDefects
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem half_unpaired_bounded_source_unique (ht : G.TriangleFree) (side : Bool)
    (hfaces : ∀ K∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side),
      ∃ F : PlaneFace G,∃ hF : F∈B.bankDefectFamily ht side,B.bankDefectPlaneFace ht side F hF=K)
    (e f : OrientedEdge (B.halfGraph side))
    (heFree : B.halfEdge side e∈G.familyUnpairedPorts (B.bankDefectFamily ht side))
    (hfDef : (B.halfGraph side).sourceFace f∈
      (B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side))
    (hc : edgeComponent f=edgeComponent e) : f=e := by
  obtain ⟨F,hF,hFace⟩ := hfaces _ hfDef
  have hfOldFace := (B.bankDefect_sourceFace_iff ht side F hF f).mp hFace.symm
  have hfOldDef : G.sourceFace (B.halfEdge side f)∈G.defectPlaneFaces ht := by
    rw [hfOldFace]
    exact (Finset.mem_filter.mp hF).1
  have hfOldPort : B.halfEdge side f∈G.familySourcePorts (B.bankDefectFamily ht side) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,G.spineSource_of_sourceFace_mem_defects ht _ hfOldDef,hfOldFace ▸ hF⟩
  have hcOld : edgeComponent (B.halfEdge side f)=edgeComponent (B.halfEdge side e) :=
    congrArg (B.halfComponentMap side) hc
  exact B.halfEdge_injective side
    (G.familyUnpairedPort_unique (B.bankDefectFamily ht side) (B.halfEdge side e) heFree
      (B.halfEdge side f) hfOldPort hcOld)

theorem half_unpaired_component_boundary (ht : G.TriangleFree) (side : Bool)
    (hfaces : ∀ K∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side),
      ∃ F : PlaneFace G,∃ hF : F∈B.bankDefectFamily ht side,B.bankDefectPlaneFace ht side F hF=K)
    (e : OrientedEdge (B.halfGraph side)) (he : SpineSource e)
    (heDef : (B.halfGraph side).sourceFace e∈
      (B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side))
    (heFree : B.halfEdge side e∈G.familyUnpairedPorts (B.bankDefectFamily ht side)) :
    edgeComponent e∈(B.halfGraph side).familyBoundaryTrackComponents
      ((B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side)) := by
  obtain ⟨t,hreach,htop⟩ := exists_spine_end e
  have hf : SpineSource (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  have hc : edgeComponent (reverseEdge t)=edgeComponent e :=
    (reverse_component t).symm.trans (positive_path_component hreach).symm
  have hne : reverseEdge t≠e := (spine_opposite_sources_ne hreach).symm
  have hext : ¬Bornology.IsBounded ((B.halfGraph side).sourceFace (reverseEdge t)).val := by
    rcases (B.halfGraph side).sourceFace_defect_or_unbounded (B.halfGraph_triangleFree ht side) _ hf with hdef | ho
    · exact False.elim (hne (B.half_unpaired_bounded_source_unique ht side hfaces e _ heFree hdef hc))
    · exact ho
  have hePort : e∈(B.halfGraph side).familySourcePorts
      ((B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heDef⟩
  have heTrack : edgeComponent e∈(B.halfGraph side).familyTrackComponents
      ((B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side)) :=
    Finset.mem_image.mpr ⟨e,hePort,rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨reverseEdge t,Finset.mem_filter.mpr ⟨?_,hext⟩,hc⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,hf,?_⟩
  rw [hc]
  exact heTrack

theorem isolated_pentagon_half_boundary_ports (ht : G.TriangleFree) (side : Bool)
    (hfaces : ∀ K∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side),
      ∃ F : PlaneFace G,∃ hF : F∈B.bankDefectFamily ht side,B.bankDefectPlaneFace ht side F hF=K)
    (F : PlaneFace G) (hF : F∈B.isolatedTwoPortPentagons ht side) :
    ∀ e∈(B.halfGraph side).faceSourcePorts
      (B.bankDefectPlaneFace ht side F (Finset.mem_filter.mp hF).1),
      edgeComponent e∈(B.halfGraph side).familyBoundaryTrackComponents
        ((B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side)) := by
  intro e he
  have heFace := (Finset.mem_filter.mp he).2.2
  have heOldFace := (B.bankDefect_sourceFace_iff ht side F (Finset.mem_filter.mp hF).1 e).mp heFace
  have heOldDef : G.sourceFace (B.halfEdge side e)∈G.defectPlaneFaces ht := by
    rw [heOldFace]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hF).1).1
  have heOldPort : B.halfEdge side e∈G.faceSourcePorts F := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,G.spineSource_of_sourceFace_mem_defects ht _ heOldDef,heOldFace⟩
  apply B.half_unpaired_component_boundary ht side hfaces e (Finset.mem_filter.mp he).2.1
  · rw [heFace]
    exact B.bankDefectPlaneFace_mem_defects ht side F (Finset.mem_filter.mp hF).1
  · exact (Finset.mem_filter.mp hF).2.2.2 _ heOldPort

end OrdinaryCutBanks
end Swanepoel
