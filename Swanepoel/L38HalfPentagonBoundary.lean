module
public import Swanepoel.L38HalfPentagonTracks
public import Swanepoel.L38HalfAreaBankFaces
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def bankPentagonBoundary (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) (P : PentagonFaceBoundary G F) :
    PentagonFaceBoundary (B.halfGraph side) (B.bankDefectPlaneFace ht side F hF) := by
  have hpf (i : Fin 5) : G.sourceFace (P.dart i)=F := P.face i
  have hv (i : Fin 5) : P.vertex i∈B.bankVertices side := by
    apply B.bank_defect_vertex_mem ht side F hF
    have h := (G.sourceFace_endpoints_mem_closure (P.dart i)).1
    change G.point (P.vertex i)∈closure (G.sourceFace (P.dart i)).val at h
    rw [hpf i] at h
    exact h
  let v (i : Fin 5) := B.halfVertexIndex side (P.vertex i) (hv i)
  have hc (i : Fin 5) : (B.halfGraph side).graph.Adj (v i) (v (i+1)) := by
    apply (B.halfGraph_adj_iff side _ _).mpr
    simpa only [v,B.halfVertex_index] using P.contact i
  let e (i : Fin 5) : OrientedEdge (B.halfGraph side) := ⟨(v i,v (i+1)),hc i⟩
  have hmap (i : Fin 5) : B.halfEdge side (e i)=P.dart i := by
    apply Subtype.ext
    exact Prod.ext (B.halfVertex_index side _ (hv i)) (B.halfVertex_index side _ (hv (i+1)))
  have hface (i : Fin 5) :
      (B.halfGraph side).sourceFace (e i)=B.bankDefectPlaneFace ht side F hF := by
    apply (B.bankDefect_sourceFace_iff ht side F hF (e i)).mpr
    rw [hmap]
    exact P.face i
  refine { vertex := v,vertex_injective := ?_,contact := hc,face := hface,darts := ?_ }
  · intro i j hij
    apply P.vertex_injective
    have h := congrArg (B.halfVertex side) hij
    simpa only [v,B.halfVertex_index] using h
  · ext f
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      have hs : SpineSource (P.dart i) := G.spineSource_of_sourceFace_mem_defects ht _
        (by rw [hpf i]; exact (Finset.mem_filter.mp hF).1)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,B.half_source_of_old side (e i) (hmap i ▸ hs),hface i⟩
    · intro hf
      have hfF := (Finset.mem_filter.mp hf).2.2
      have holdF := (B.bankDefect_sourceFace_iff ht side F hF f).mp hfF
      have holdport : B.halfEdge side f∈G.faceSourcePorts F := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,G.spineSource_of_sourceFace_mem_defects ht _
          (by rw [holdF]; exact (Finset.mem_filter.mp hF).1),holdF⟩
      rw [← P.darts] at holdport
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp holdport
      exact ⟨i,B.halfEdge_injective side ((hmap i).trans hi)⟩

theorem bankPentagonBoundary_dart (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) (P : PentagonFaceBoundary G F) (i : Fin 5) :
    B.halfEdge side ((B.bankPentagonBoundary ht side F hF P).dart i)=P.dart i := by
  apply Subtype.ext
  exact Prod.ext (B.halfVertex_index side _ _) (B.halfVertex_index side _ _)

theorem bankPentagonBoundary_normal (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) (P : PentagonFaceBoundary G F) (i : Fin 5) :
    (B.bankPentagonBoundary ht side F hF P).normal i=P.normal i := by
  unfold PentagonFaceBoundary.normal
  rw [← (B.halfPentagonEmbedding side).mapEdge_normal]
  change sourceNormal (B.halfEdge side ((B.bankPentagonBoundary ht side F hF P).dart i))=sourceNormal (P.dart i)
  rw [B.bankPentagonBoundary_dart]

def bankPentagonBins (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) (P : PentagonFaceBoundary G F)
    {ρ : ℝ} (D : P.BankBinData ρ) : (B.bankPentagonBoundary ht side F hF P).BankBinData ρ where
  angle := D.angle
  bounds := D.bounds
  phase i := by rw [B.bankPentagonBoundary_normal]; exact D.phase i

def bankPentagonSectorAngles (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) (P : PentagonFaceBoundary G F)
    {j : Fin 5} (D : P.SectorAngleData j) : (B.bankPentagonBoundary ht side F hF P).SectorAngleData j where
  rho := D.rho
  a := D.a
  b := D.b
  g := D.g
  a_pos := D.a_pos
  a_lt_two := D.a_lt_two
  b_pos := D.b_pos
  b_lt_two := D.b_lt_two
  g_pos := D.g_pos
  g_lt_two := D.g_lt_two
  phase_base := by rw [B.bankPentagonBoundary_normal]; exact D.phase_base
  phase_prev := by rw [B.bankPentagonBoundary_normal]; exact D.phase_prev
  phase_next := by rw [B.bankPentagonBoundary_normal]; exact D.phase_next
  phase_next_next := by rw [B.bankPentagonBoundary_normal]; exact D.phase_next_next
  pair_left := D.pair_left
  pair_right := D.pair_right
  triple := D.triple

end OrdinaryCutBanks
end Swanepoel
