module
public import Swanepoel.L38HalfPentagonCrossings
public import Swanepoel.L38HalfAreaFamilyTracks
public import Swanepoel.L38BankCrossingRealization
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem TrackSystem.l38_crossings_comm (D : TrackSystem) (A B : Finset D.Track) :
    D.crossings A B=D.crossings B A := by
  unfold TrackSystem.crossings
  refine Finset.card_bij (fun p _ => (p.2,p.1)) ?_ ?_ ?_
  · intro p hp
    have h := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp h.1).2,(Finset.mem_product.mp h.1).1⟩,D.crossing.adj_symm h.2⟩
  · intro p _ q _ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro q hq
    have h := Finset.mem_filter.mp hq
    exact ⟨(q.2,q.1),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp h.1).2,(Finset.mem_product.mp h.1).1⟩,D.crossing.adj_symm h.2⟩,rfl⟩

theorem PennyGraph.l38_interFamilyCrossings_comm {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y Z : Finset (PlaneFace G)) :
    G.interFamilyCrossings ht Y Z=G.interFamilyCrossings ht Z Y :=
  TrackSystem.l38_crossings_comm _ _ _

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bankDefectImage_crossing_iff (ht : G.TriangleFree) (side : Bool)
    (Y Z : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) (hZ : Z⊆B.bankDefectFamily ht side)
    {c d : TrackComponent (B.halfGraph side)}
    (hc : c∈(B.halfGraph side).familyTrackComponents (B.bankDefectImage ht side Y hY))
    (hd : d∈(B.halfGraph side).familyTrackComponents (B.bankDefectImage ht side Z hZ)) :
    ComponentCrosses c d↔ComponentCrosses (B.halfComponentMap side c) (B.halfComponentMap side d) := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hd
  have heOld : B.halfEdge side e∈G.familySourcePorts Y := by
    rw [← B.bankDefectImage_sourcePorts_image ht side Y hY]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hfOld : B.halfEdge side f∈G.familySourcePorts Z := by
    rw [← B.bankDefectImage_sourcePorts_image ht side Z hZ]
    exact Finset.mem_image.mpr ⟨f,hf,rfl⟩
  exact B.half_old_source_crossing_iff ht side e f
    (Finset.mem_filter.mp heOld).2.1 (Finset.mem_filter.mp hfOld).2.1

theorem bankDefectImage_inter_crossings (ht : G.TriangleFree) (side : Bool)
    (Y Z : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) (hZ : Z⊆B.bankDefectFamily ht side) :
    (B.halfGraph side).interFamilyCrossings (B.halfGraph_triangleFree ht side)
      (B.bankDefectImage ht side Y hY) (B.bankDefectImage ht side Z hZ)=G.interFamilyCrossings ht Y Z := by
  let H := B.halfGraph side
  have hinjA := B.bankDefectImage_tracks_map_injOn ht side Y hY
  have hinjC := B.bankDefectImage_tracks_map_injOn ht side Z hZ
  rw [H.interFamilyCrossings_eq_degree_sum (B.halfGraph_triangleFree ht side),
    G.interFamilyCrossings_eq_degree_sum ht,
    ← B.bankDefectImage_tracks_image ht side Y hY,← B.bankDefectImage_tracks_image ht side Z hZ,
    Finset.sum_image (fun c hc d hd h => hinjC hc hd h)]
  apply Finset.sum_congr rfl
  intro c hc
  unfold PennyGraph.familyCrossingDegree
  rw [Finset.filter_image,Finset.card_image_of_injOn
    (hinjA.mono (Finset.filter_subset _ _))]
  congr 1
  apply Finset.filter_congr
  intro a ha
  exact B.bankDefectImage_crossing_iff ht side Y Z hY hZ ha hc

theorem bankDefectImage_internal_crossings (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.halfGraph side).familyInternalCrossings (B.halfGraph_triangleFree ht side)
      (B.bankDefectImage ht side Y hY)=G.familyInternalCrossings ht Y := by
  let H := B.halfGraph side
  let D := componentSystem H (B.halfGraph_triangleFree ht side) ∅ 0
  let E := componentSystem G ht ∅ 0
  let eh := Fintype.equivFin (TrackComponent H)
  let eg := Fintype.equivFin (TrackComponent G)
  let A := H.familyTrackIndices (B.bankDefectImage ht side Y hY)
  let f : Fin (Fintype.card (TrackComponent H))→Fin (Fintype.card (TrackComponent G)) :=
    fun u => eg (B.halfComponentMap side (eh.symm u))
  have hmem (u) (hu : u∈A) : eh.symm u∈H.familyTrackComponents (B.bankDefectImage ht side Y hY) := by
    obtain ⟨c,hc,hcu⟩ := Finset.mem_map.mp hu
    rw [← hcu]
    change eh.symm (eh c)∈H.familyTrackComponents (B.bankDefectImage ht side Y hY)
    rw [eh.symm_apply_apply]
    exact hc
  have hinj : Set.InjOn f (A : Set (Fin (Fintype.card (TrackComponent H)))) := by
    intro u hu v hv h
    apply eh.symm.injective
    apply B.bankDefectImage_tracks_map_injOn ht side Y hY (hmem u hu) (hmem v hv)
    exact eg.injective h
  have hAdj : ∀ u∈A,∀ v∈A,E.crossing.Adj (f u) (f v)↔D.crossing.Adj u v := by
    intro u hu v hv
    change ComponentCrosses (eg.symm (f u)) (eg.symm (f v))↔ComponentCrosses (eh.symm u) (eh.symm v)
    simpa only [f,Equiv.symm_apply_apply] using
      (B.bankDefectImage_crossing_iff ht side Y Y hY hY (hmem u hu) (hmem v hv)).symm
  have himage : A.image f=G.familyTrackIndices Y := by
    change (H.familyTrackIndices (B.bankDefectImage ht side Y hY)).image f=G.familyTrackIndices Y
    rw [PennyGraph.familyTrackIndices,Finset.map_eq_image,Finset.image_image]
    have hfun : (fun c : TrackComponent H => f (eh c))=(fun c => eg (B.halfComponentMap side c)) := by
      funext c
      simp only [f,Equiv.symm_apply_apply]
    change (H.familyTrackComponents (B.bankDefectImage ht side Y hY)).image (fun c => f (eh c))=_
    rw [hfun]
    calc
      _ = ((H.familyTrackComponents (B.bankDefectImage ht side Y hY)).image (B.halfComponentMap side)).image eg :=
        (Finset.image_image (s := H.familyTrackComponents (B.bankDefectImage ht side Y hY))
          (f := B.halfComponentMap side) (g := eg)).symm
      _ = (G.familyTrackComponents Y).image eg := by rw [B.bankDefectImage_tracks_image ht side Y hY]
      _ = G.familyTrackIndices Y := (Finset.map_eq_image eg.toEmbedding _).symm
  have hcount := D.internal_image_of_injOn E A f hinj hAdj
  have htarget : E.internal (A.image f)=G.familyInternalCrossings ht Y := congrArg E.internal himage
  exact hcount.symm.trans htarget

theorem bankDefectImage_R (ht : G.TriangleFree) (side : Bool)
    (Y : Finset (PlaneFace G)) (hY : Y⊆B.bankDefectFamily ht side) :
    (B.halfGraph side).familyR (B.halfGraph_triangleFree ht side) (B.bankDefectImage ht side Y hY)=
      G.familyR ht Y := by
  unfold PennyGraph.familyR
  rw [B.bankDefectImage_internal_crossings ht side Y hY,B.bankDefectImage_card ht side Y hY]

end OrdinaryCutBanks
end Swanepoel
