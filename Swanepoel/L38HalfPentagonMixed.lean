module
public import Swanepoel.L38HalfPentagonBoundary
public import Swanepoel.L38HalfAreaDefects
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PentagonSpokeLoops.mixed_bound_of_local_angle_data {n : ℕ} {G : PennyGraph n}
    {F : PlaneFace G} {P : PentagonFaceBoundary G F} (K : PentagonSpokeLoops G F P)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (hangles : ∀ j : Fin 5,Nonempty (P.SectorAngleData j))
    (hslots : ∀ H∈Y\{F},∀ axis : Bool→Plane,(∀ b,‖axis b‖=1) →
      (∑ e∈G.faceSourcePorts H,twoConeSlots axis (sourceNormal e))+6≤2*(G.faceSourcePorts H).card) :
    (G.interFamilyCrossings ht {F} (Y\{F}) : ℤ)+G.familyJoinCount (Y\{F})≤
      2*((G.familySourcePorts (Y\{F})).card : ℤ)-6*(Y\{F}).card := by
  have hex (j : Fin 5) := (Classical.choice (hangles j)).exists_covering_axes
  choose axes hnorm hsep hcover using hex
  let axis (code : Fin 5→ℤ) := axes (K.codeSector code)
  have haxis : ∀ code b,‖axis code b‖=1 := fun code b => hnorm (K.codeSector code) b
  have hcapacity : ∀ e∈G.familySourcePorts (Y\{F}),
      G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)≤
        twoConeSlots (axis (K.code (G.sourceFace e))) (sourceNormal e) := by
    intro e he
    have hmem := (Finset.mem_filter.mp he).2
    have heY := (Finset.mem_sdiff.mp hmem.2).1
    have heRoot : G.sourceFace e≠F := by
      intro heq
      exact (Finset.mem_sdiff.mp hmem.2).2 (Finset.mem_singleton.mpr heq)
    have hdata := K.source_crossing_data ht hY hFY hports e (hY.subset_defects heY) heRoot
    exact hcover (K.faceSector (G.sourceFace e)) (sourceNormal e) (sourceNormal_norm e) _
      hdata.1 hdata.2.1 hdata.2.2
  let Z := Y\{F}
  have hZ : G.IsJoinClosed ht Z := hY.sdiff (G.boundary_face_singleton_joinClosed ht hY F hFY hports)
  let slot (e : OrientedEdge G) := twoConeSlots (axis (K.code (G.sourceFace e))) (sourceNormal e)
  have hport (i : Fin 5) : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hsilent (c : TrackComponent G) (hc : c∈G.familyJoinTrackComponents Z)
      (hz : G.familyCrossingDegree (G.familyTrackComponents {F}) c=0) :
      1≤∑ e∈G.familyPortFiber Z c,slot e := by
    obtain ⟨e,f,hne,hpair⟩ := Finset.card_eq_two.mp (G.join_port_fiber_card_two ht hZ c hc)
    have he : e∈G.familyPortFiber Z c := by rw [hpair]; simp
    have hf : f∈G.familyPortFiber Z c := by rw [hpair]; simp
    have he' := Finset.mem_filter.mp he
    have hf' := Finset.mem_filter.mp hf
    have hePort := (Finset.mem_filter.mp he'.1).2
    have hfPort := (Finset.mem_filter.mp hf'.1).2
    have heDef := hZ.subset_defects hePort.2
    have hfDef := hZ.subset_defects hfPort.2
    have heRoot : G.sourceFace e≠F := by
      intro h
      exact (Finset.mem_sdiff.mp hePort.2).2 (Finset.mem_singleton.mpr h)
    have hfRoot : G.sourceFace f≠F := by
      intro h
      exact (Finset.mem_sdiff.mp hfPort.2).2 (Finset.mem_singleton.mpr h)
    have hcomp := hf'.2.trans he'.2.symm
    have hmiss (i : Fin 5) : ¬ComponentCrosses (edgeComponent e) (edgeComponent (P.dart i)) := by
      intro hx
      have hA : edgeComponent (P.dart i)∈G.familyTrackComponents {F} := by
        rw [PennyGraph.familyTrackComponents,G.familySourcePorts_singleton]
        exact Finset.mem_image.mpr ⟨P.dart i,hport i,rfl⟩
      have hx' : ComponentCrosses (edgeComponent (P.dart i)) c := by
        rw [← he'.2]
        exact (componentGraph G ht).adj_symm hx
      have hempty : ((G.familyTrackComponents {F}).filter (fun a => ComponentCrosses a c))=∅ :=
        Finset.card_eq_zero.mp hz
      have hmem : edgeComponent (P.dart i)∈
          (G.familyTrackComponents {F}).filter (fun a => ComponentCrosses a c) :=
        Finset.mem_filter.mpr ⟨hA,hx'⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    have hcode := K.zero_crossing_join_code_eq ht hY hFY hports e f heDef hfDef heRoot hfRoot hcomp hmiss
    have hn := source_normals_opposite ht hePort.1 hfPort.1 hcomp (Ne.symm hne)
    rw [hpair,Finset.sum_pair hne]
    change 1≤twoConeSlots (axis (K.code (G.sourceFace e))) (sourceNormal e)+
      twoConeSlots (axis (K.code (G.sourceFace f))) (sourceNormal f)
    rw [← hcode,hn]
    exact twoConeSlots_antipodal_cover _ _ (haxis _) (sourceNormal_norm e) (hsep _)
  have hcount := G.mixed_crossings_add_joins_le_slots ht {F} hZ slot hcapacity hsilent
  have htotal : (∑ H∈Z,∑ e∈G.faceSourcePorts H,twoConeSlots (axis (K.code H)) (sourceNormal e))=
      ∑ e∈G.familySourcePorts Z,slot e := by
    have hfib := Finset.sum_fiberwise_of_maps_to
      (fun e he => (Finset.mem_filter.mp he).2.2 : ∀ e∈G.familySourcePorts Z,G.sourceFace e∈Z) slot
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro H hH
    have hset : (G.familySourcePorts Z).filter (fun e => G.sourceFace e=H)=G.faceSourcePorts H := by
      ext e
      simp only [PennyGraph.familySourcePorts,PennyGraph.faceSourcePorts,Finset.mem_filter,
        Finset.mem_univ,true_and]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2 ▸ hH⟩,h.2⟩⟩
    rw [hset]
    exact Finset.sum_congr rfl (fun e he => by
      dsimp only [slot]
      rw [(Finset.mem_filter.mp he).2.2])
  have hsum := Finset.sum_le_sum (fun H hH => hslots H hH (axis (K.code H)) (haxis _))
  have hupper : (∑ e∈G.familySourcePorts Z,slot e)+6*Z.card≤2*(G.familySourcePorts Z).card := by
    rw [G.familySourcePorts_card,← htotal]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,Finset.mul_sum,Nat.mul_comm] using hsum
  have hnat : G.interFamilyCrossings ht {F} Z+G.familyJoinCount Z+6*Z.card≤2*(G.familySourcePorts Z).card := by omega
  have hint : (G.interFamilyCrossings ht {F} Z : ℤ)+G.familyJoinCount Z+6*(Z.card : ℤ)≤
      2*((G.familySourcePorts Z).card : ℤ) := by exact_mod_cast hnat
  change (G.interFamilyCrossings ht {F} Z : ℤ)+G.familyJoinCount Z≤
    2*((G.familySourcePorts Z).card : ℤ)-6*Z.card
  omega

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bankDefect_two_cone_slots_face_bound (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side)
    (axis : Bool→Plane) (haxis : ∀ b,‖axis b‖=1) :
    (∑ e∈(B.halfGraph side).faceSourcePorts (B.bankDefectPlaneFace ht side F hF),
      twoConeSlots axis (sourceNormal e))+6≤
        2*((B.halfGraph side).faceSourcePorts (B.bankDefectPlaneFace ht side F hF)).card := by
  have h := G.two_cone_slots_face_bound ht F (Finset.mem_filter.mp hF).1 hdegree axis haxis
  have hsum : (∑ e∈G.faceSourcePorts F,twoConeSlots axis (sourceNormal e))=
      ∑ e∈(B.halfGraph side).faceSourcePorts (B.bankDefectPlaneFace ht side F hF),
        twoConeSlots axis (sourceNormal e) := by
    rw [← B.bankDefect_sourcePorts_image ht side F hF,
      Finset.sum_image (fun e _ f _ h => B.halfEdge_injective side h)]
    apply Finset.sum_congr rfl
    intro e _
    rw [show sourceNormal (B.halfEdge side e)=sourceNormal e from
      (B.halfPentagonEmbedding side).mapEdge_normal e]
  rw [hsum,← B.bankDefect_sourcePorts_card ht side F hF] at h
  exact h

theorem half_pentagon_crossing_estimate_of_bank_faces (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hfaces : ∀ K∈(B.halfGraph side).defectPlaneFaces (B.halfGraph_triangleFree ht side),
      ∃ F : PlaneFace G,∃ hF : F∈B.bankDefectFamily ht side,B.bankDefectPlaneFace ht side F hF=K) :
    (B.halfGraph side).PentagonCrossingEstimate (B.halfGraph_triangleFree ht side) := by
  intro Y hY K hKY hfive hports
  obtain ⟨F,hF,rfl⟩ := hfaces K (hY.subset_defects hKY)
  have hfiveOld : (G.faceSourcePorts F).card=5 := by
    rwa [B.bankDefect_sourcePorts_card ht side F hF] at hfive
  obtain ⟨P⟩ := G.five_port_face_boundary ht F (Finset.mem_filter.mp hF).1 hdegree hfiveOld
  let Q := B.bankPentagonBoundary ht side F hF P
  obtain ⟨loops⟩ := Q.exists_spoke_loops (B.halfGraph_triangleFree ht side) hY hKY hports
  apply loops.mixed_bound_of_local_angle_data (B.halfGraph_triangleFree ht side) hY hKY hports
  · intro j
    obtain ⟨D⟩ := P.exists_sector_angle_data ht (Finset.mem_filter.mp hF).1 hdegree j
    exact ⟨B.bankPentagonSectorAngles ht side F hF P D⟩
  · intro L hL axis haxis
    obtain ⟨H,hH,rfl⟩ := hfaces L (hY.subset_defects (Finset.mem_sdiff.mp hL).1)
    exact B.bankDefect_two_cone_slots_face_bound ht side hdegree H hH axis haxis

end OrdinaryCutBanks
end Swanepoel
