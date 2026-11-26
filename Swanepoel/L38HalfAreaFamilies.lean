module
public import Swanepoel.L38HalfAreaDefects
public import Swanepoel.L38BankPartition
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def bankDefectImage (ht : G.TriangleFree) (side : Bool) (Y : Finset (PlaneFace G))
    (hY : Y⊆B.bankDefectFamily ht side) : Finset (PlaneFace (B.halfGraph side)) :=
  Y.attach.image (fun F => B.bankDefectPlaneFace ht side F.val (hY F.property))

theorem bankDefectImage_mem (ht : G.TriangleFree) (side : Bool) (Y : Finset (PlaneFace G))
    (hY : Y⊆B.bankDefectFamily ht side) (F : PlaneFace G) (hF : F∈Y) :
    B.bankDefectPlaneFace ht side F (hY hF)∈B.bankDefectImage ht side Y hY :=
  Finset.mem_image.mpr ⟨⟨F,hF⟩,Finset.mem_attach _ _,rfl⟩

theorem bankDefectImage_singleton (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    B.bankDefectImage ht side {F} (Finset.singleton_subset_iff.mpr hF)=
      {B.bankDefectPlaneFace ht side F hF} := by
  apply Finset.Subset.antisymm
  · intro K hK
    obtain ⟨L,_,hMap⟩ := Finset.mem_image.mp hK
    have hLF : L.val=F := Finset.mem_singleton.mp L.property
    have hSame : B.bankDefectPlaneFace ht side L.val
        ((Finset.singleton_subset_iff.mpr hF) L.property)=B.bankDefectPlaneFace ht side F hF := by
      apply Subtype.ext
      change L.val.val=F.val
      exact congrArg (fun J : PlaneFace G => J.val) hLF
    exact Finset.mem_singleton.mpr (hMap.symm.trans hSame)
  · intro K hK
    rw [Finset.mem_singleton.mp hK]
    exact B.bankDefectImage_mem ht side {F} (Finset.singleton_subset_iff.mpr hF) F (Finset.mem_singleton_self F)

theorem bankDefectImage_subset_defects (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    B.bankDefectImage ht side Y hY⊆
      (B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side) := by
  intro K hK
  obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp hK
  exact B.bankDefectPlaneFace_mem_defects ht side F.val (hY F.property)

theorem bankDefectImage_card (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.bankDefectImage ht side Y hY).card=Y.card := by
  have hinj : Function.Injective (fun F : {F : PlaneFace G // F∈Y} =>
      B.bankDefectPlaneFace ht side F.val (hY F.property)) := by
    intro F K h
    have hval := congrArg (fun L : PlaneFace (B.halfGraph side) => L.val) h
    change F.val.val=K.val.val at hval
    exact Subtype.ext (Subtype.ext hval)
  rw [bankDefectImage,Finset.card_image_of_injective _ hinj,Finset.card_attach]

theorem bankDefectImage_sourcePorts_image (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    ((B.halfGraph side).familySourcePorts (B.bankDefectImage ht side Y hY)).image (B.halfEdge side)=
      G.familySourcePorts Y := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    have hfp := (Finset.mem_filter.mp hf).2
    obtain ⟨F,_,hFace⟩ := Finset.mem_image.mp hfp.2
    have hOldFace := (B.bankDefect_sourceFace_iff ht side F.val (hY F.property) f).mp hFace.symm
    have hOldDef : G.sourceFace (B.halfEdge side f)∈G.defectPlaneFaces ht :=
      hOldFace ▸ (Finset.mem_filter.mp (hY F.property)).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      G.spineSource_of_sourceFace_mem_defects ht _ hOldDef,hOldFace ▸ F.property⟩
  · intro he
    have hep := (Finset.mem_filter.mp he).2
    have hv := B.bank_defect_source_vertices ht side e (hY hep.2)
    let f := B.liftHalfEdge side e hv.1 hv.2
    have hFace : (B.halfGraph side).sourceFace f=
        B.bankDefectPlaneFace ht side (G.sourceFace e) (hY hep.2) := by
      apply (B.bankDefect_sourceFace_iff ht side (G.sourceFace e) (hY hep.2) f).mpr
      rw [B.halfEdge_lift side e hv.1 hv.2]
    refine Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,
      B.halfEdge_lift side e hv.1 hv.2⟩
    · exact B.bank_source_lift_is_source side e hv.1 hv.2 hep.1
    · rw [hFace]
      exact B.bankDefectImage_mem ht side Y hY (G.sourceFace e) hep.2

theorem bankDefectImage_sourcePorts_card (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    ((B.halfGraph side).familySourcePorts (B.bankDefectImage ht side Y hY)).card=
      (G.familySourcePorts Y).card := by
  rw [← B.bankDefectImage_sourcePorts_image ht side Y hY,
    Finset.card_image_of_injective _ (B.halfEdge_injective side)]

theorem bankDefectImage_portExcess (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.halfGraph side).familyPortExcess (B.bankDefectImage ht side Y hY)=G.familyPortExcess Y := by
  have hH := (B.halfGraph side).partial_family_bank_identities (B.halfGraph_triangleFree ht side)
    (B.bankDefectImage ht side Y hY)
  have hG := G.partial_family_bank_identities ht Y
  have hL := B.bankDefectImage_sourcePorts_card ht side Y hY
  have hF := B.bankDefectImage_card ht side Y hY
  have hLZ : (((B.halfGraph side).familySourcePorts (B.bankDefectImage ht side Y hY)).card : ℤ)=
      (G.familySourcePorts Y).card := by exact_mod_cast hL
  have hFZ : ((B.bankDefectImage ht side Y hY).card : ℤ)=Y.card := by exact_mod_cast hF
  omega

theorem bankDefectImage_disjoint (ht : G.TriangleFree) (side : Bool)
    (Y Z : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side)
    (hZ : Z⊆B.bankDefectFamily ht side) (hYZ : Disjoint Y Z) :
    Disjoint (B.bankDefectImage ht side Y hY) (B.bankDefectImage ht side Z hZ) := by
  apply Finset.disjoint_left.mpr
  intro K hKY hKZ
  obtain ⟨F,_,hF⟩ := Finset.mem_image.mp hKY
  obtain ⟨L,_,hL⟩ := Finset.mem_image.mp hKZ
  have hval := congrArg (fun J : PlaneFace (B.halfGraph side) => J.val) (hF.trans hL.symm)
  change F.val.val=L.val.val at hval
  have hFL : F.val=L.val := Subtype.ext hval
  exact Finset.disjoint_left.mp hYZ F.property (hFL.symm ▸ L.property)

end OrdinaryCutBanks
end Swanepoel
