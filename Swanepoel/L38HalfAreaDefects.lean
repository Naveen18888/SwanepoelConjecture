module
public import Swanepoel.L38HalfAreaBankFaces
public import Swanepoel.L38HalfPentagonEmbedding
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bank_source_lift_is_source (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side)
    (he : SpineSource e) : SpineSource (B.liftHalfEdge side e ha hb) := by
  let E : L38HalfPentagonEmbedding (B.halfGraph side) G :=
    ⟨B.halfVertex side,B.halfVertex_injective side,B.halfGraph_point side⟩
  apply E.source_of_source_map
  change SpineSource (B.halfEdge side (B.liftHalfEdge side e ha hb))
  rwa [B.halfEdge_lift side e ha hb]

theorem bankDefectPlaneFace_mem_defects (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    B.bankDefectPlaneFace ht side F hF∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side) := by
  have hfive := G.defect_source_ports_five_le ht F (Finset.mem_filter.mp hF).1
  have hpos : 0<(G.faceSourcePorts F).card := by omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
  have hep := (Finset.mem_filter.mp he).2
  have heBank : G.sourceFace e∈B.bankDefectFamily ht side := hep.2 ▸ hF
  have hv := B.bank_defect_source_vertices ht side e heBank
  let f := B.liftHalfEdge side e hv.1 hv.2
  have hfSource : SpineSource f := B.bank_source_lift_is_source side e hv.1 hv.2 hep.1
  have hfFace : (B.halfGraph side).sourceFace f=B.bankDefectPlaneFace ht side F hF := by
    apply (B.bankDefect_sourceFace_iff ht side F hF f).mpr
    rw [B.halfEdge_lift side e hv.1 hv.2]
    exact hep.2
  rcases (B.halfGraph side).sourceFace_defect_or_unbounded (B.halfGraph_triangleFree ht side) f hfSource with hd | ho
  · rwa [hfFace] at hd
  · have hb := G.defectPlaneFace_isBounded ht (Finset.mem_filter.mp hF).1
    rw [hfFace] at ho
    exact False.elim (ho hb)

theorem bankDefect_sourcePorts_image (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    ((B.halfGraph side).faceSourcePorts (B.bankDefectPlaneFace ht side F hF)).image (B.halfEdge side)=
      G.faceSourcePorts F := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    have hfp := (Finset.mem_filter.mp hf).2
    have hfFace := (B.bankDefect_sourceFace_iff ht side F hF f).mp hfp.2
    have hOldDef : G.sourceFace (B.halfEdge side f)∈G.defectPlaneFaces ht :=
      hfFace ▸ (Finset.mem_filter.mp hF).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      G.spineSource_of_sourceFace_mem_defects ht _ hOldDef,hfFace⟩
  · intro he
    have hep := (Finset.mem_filter.mp he).2
    have heBank : G.sourceFace e∈B.bankDefectFamily ht side := hep.2 ▸ hF
    have hv := B.bank_defect_source_vertices ht side e heBank
    let f := B.liftHalfEdge side e hv.1 hv.2
    refine Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,
      B.halfEdge_lift side e hv.1 hv.2⟩
    · exact B.bank_source_lift_is_source side e hv.1 hv.2 hep.1
    · apply (B.bankDefect_sourceFace_iff ht side F hF f).mpr
      rw [B.halfEdge_lift side e hv.1 hv.2]
      exact hep.2

theorem bankDefect_sourcePorts_card (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    ((B.halfGraph side).faceSourcePorts (B.bankDefectPlaneFace ht side F hF)).card=
      (G.faceSourcePorts F).card := by
  rw [← B.bankDefect_sourcePorts_image ht side F hF,
    Finset.card_image_of_injective _ (B.halfEdge_injective side)]

theorem half_defect_area_lower_of_bank_face_surjective (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hfaces : ∀ K∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side),
      ∃ F : PlaneFace G,∃ hF : F∈B.bankDefectFamily ht side,B.bankDefectPlaneFace ht side F hF=K) :
    (B.halfGraph side).DefectAreaLowerBound (B.halfGraph_triangleFree ht side) := by
  intro K hK
  obtain ⟨F,hF,rfl⟩ := hfaces K hK
  exact B.bankDefect_signed_area_lower ht side hdegree F hF

end OrdinaryCutBanks
end Swanepoel
